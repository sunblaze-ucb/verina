from enum import Enum
from typing import Dict, List, Literal, Optional, Tuple, Type
from uuid import uuid4

from prefect import task
from prefect.cache_policies import INPUTS, TASK_SOURCE
from pydantic import BaseModel

from verina.benchmark.common import BenchmarkSpecEvaluationConfig, CoqEvaluationConfig
from verina.benchmark.report import EvaluationTaskArtifact
from verina.dataset.schema import BenchmarkData, RejectInput, TestCase
from verina.dataset.template import LeanGenerationTaskTemplate
from verina.itp import ITPType, get_compiler, get_template_class
from verina.itp.base import ITPCompiler, ITPTemplate
from verina.lean import (
    check_lean_compile,
    create_lean_file,
)

# Global compiler configuration (set by set_compiler_config)
_compiler_config: Dict[ITPType, Dict] = {}


def set_compiler_config(itp_type: ITPType, **kwargs) -> None:
    """Set global compiler configuration for an ITP type.

    This is used to pass configuration like docker_image to the compiler
    without threading it through all function calls.

    Args:
        itp_type: The ITP type.
        **kwargs: Compiler constructor arguments (e.g., docker_image='verina-coq').
    """
    _compiler_config[itp_type] = kwargs


def get_compiler_config(itp_type: ITPType) -> Dict:
    """Get the global compiler configuration for an ITP type."""
    return _compiler_config.get(itp_type, {})


def split_message(
    message: str, unique_markers: List[str], *, remove_first: bool
) -> List[str]:
    """
    Split a message into parts based on unique markers.
    """
    parts = []
    for marker in unique_markers:
        if marker in message:
            splitted = message.split(marker)
            assert len(splitted) == 2, (
                f"Message should be split into 2 parts: {splitted}"
            )
            parts.append(splitted[0])
            message = splitted[1]
    parts.append(message)
    if remove_first:
        parts = parts[1:]
    return parts


class MetricScore(BaseModel):
    pass


@task(
    cache_policy=(INPUTS - "file_name") + TASK_SOURCE,
    timeout_seconds=400,  # Coq with hammer needs longer timeout (300s compile + buffer)
)
async def metric_itp_compile(
    itp_type: ITPType,
    content: str,
    file_name: Optional[str] = None,
) -> Tuple[bool, str]:
    """
    Check if the generated ITP code compiles.

    Args:
        itp_type: The ITP type (lean or coq).
        content: The source code content.
        file_name: Optional file name. If not provided, a UUID will be used.

    Returns:
        A tuple of (success, message).

    Note:
        Uses global compiler config set by set_compiler_config().
        For Coq with QuickChick, call set_compiler_config(ITPType.COQ, docker_image='verina-coq').
    """
    if file_name is None:
        file_name = str(uuid4())
    compiler_kwargs = get_compiler_config(itp_type)
    compiler = get_compiler(itp_type, **compiler_kwargs)
    source_file = compiler.create_source_file(file_name, content)
    # Use longer timeout for Coq (hammer is slow)
    timeout = 300 if itp_type == ITPType.COQ else 120
    return compiler.check_compile(source_file, timeout=timeout)


@task(
    cache_policy=(INPUTS - "file_name") + TASK_SOURCE,
    timeout_seconds=200,
)
async def metric_lean_compile(
    lean_content: str, file_name: Optional[str] = None
) -> Tuple[bool, str]:
    """
    Check if the generated Lean code compiles.

    This is a convenience wrapper around metric_itp_compile for Lean.
    """
    return await metric_itp_compile(ITPType.LEAN, lean_content, file_name)


@task(
    cache_policy=(INPUTS - "file_name") + TASK_SOURCE,
    timeout_seconds=400,  # Coq with hammer needs longer timeout
)
async def metric_coq_compile(
    coq_content: str, file_name: Optional[str] = None
) -> Tuple[bool, str]:
    """
    Check if the generated Coq code compiles.

    This is a convenience wrapper around metric_itp_compile for Coq.
    """
    return await metric_itp_compile(ITPType.COQ, coq_content, file_name)


class LeanTestScore(Enum):
    """Test score enum for ITP evaluation.

    Named LeanTestScore for backward compatibility, but used for all ITPs.
    """
    PASS = "pass"
    FAIL = "fail"
    UNKNOWN = "unknown"


# Alias for generic ITP usage (same as LeanTestScore for backward compatibility)
ITPTestScore = LeanTestScore


class CodeMetricScore(MetricScore):
    can_compile: bool
    score: LeanTestScore = LeanTestScore.UNKNOWN
    unit_tests: Dict[int, LeanTestScore]

    def update_score(self):
        if not self.can_compile:
            self.score = LeanTestScore.FAIL
            return
        test_scores = list(self.unit_tests.values())
        if LeanTestScore.FAIL in test_scores:
            self.score = LeanTestScore.FAIL
        elif LeanTestScore.UNKNOWN in test_scores:
            self.score = LeanTestScore.UNKNOWN
        else:
            self.score = LeanTestScore.PASS


async def metric_generated_code_unit_tests(
    template_engine: ITPTemplate,
    generated_code_content: str,
    test_cases: List[TestCase],
    itp_type: ITPType = ITPType.LEAN,
) -> Dict[int, LeanTestScore]:
    content = (
        template_engine.render_test_imports() + "\n" + generated_code_content
    )

    for idx, test_case in enumerate(test_cases):
        content += "\n\n" + template_engine.render_code_unit_test(
            test_case, test_idx=idx
        )

    can_compile, compile_msg = await metric_itp_compile(itp_type, content)

    scores: Dict[int, LeanTestScore] = {}

    if can_compile:
        for idx in range(len(test_cases)):
            scores[idx] = LeanTestScore.PASS
        return scores

    code_unit_test_start_marker = f"<{template_engine.CODE_TEST_MSG_MARKER}>"
    code_unit_test_end_marker = f"</{template_engine.CODE_TEST_MSG_MARKER}>"
    code_msgs = compile_msg.split(code_unit_test_start_marker)[1:]
    code_msg_map: Dict[int, str] = {}
    for code_msg in code_msgs:
        code_msg = code_msg.split(code_unit_test_end_marker)
        assert len(code_msg) == 2, f"Code msg should be split into 2 parts: {code_msg}"
        code_msg_map[int(code_msg[0])] = code_msg[1]

    scores: Dict[int, LeanTestScore] = {}

    for idx, test_case in enumerate(test_cases):
        msg = code_msg_map.get(idx, "")
        if msg == "":
            # No message for this test - compile failed before reaching this test
            # This means the code has an error, so the test should fail
            scores[idx] = LeanTestScore.FAIL
        elif template_engine.DECIDABLE_ERR_MSG in msg:
            scores[idx] = LeanTestScore.FAIL
        elif "error" in msg.lower():
            # Error in test evaluation (not expected for code tests)
            scores[idx] = LeanTestScore.UNKNOWN
        else:
            scores[idx] = LeanTestScore.PASS

    return scores


async def metric_generated_code(
    template_engine: ITPTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    precond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> CodeMetricScore:
    # Select appropriate data based on ITP type
    if itp_type == ITPType.COQ:
        itp_data = benchmark_data.coq_data
        no_precond_default = "True (* no precondition *)"
    else:
        itp_data = benchmark_data.lean_data
        no_precond_default = "True -- no precondition"

    content = (
        template_engine.render_imports(itp_data.task_imports, "task")
        + "\n"
    )
    content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    content += (
        template_engine.render_aux(itp_data.task_aux, "task") + "\n"
    )

    content += template_engine.render_aux(artifact.precond_aux, "precond") + "\n"
    precond = artifact.precond
    if precond == "":
        precond = no_precond_default
    content += (
        template_engine.render_precond(precond, precond_name=precond_name) + "\n"
    )

    content += template_engine.render_aux(artifact.code_aux, "code") + "\n"
    content += (
        template_engine.render_code(artifact.code, precond_name=precond_name) + "\n"
    )

    can_compile, compile_err = await metric_itp_compile(itp_type, content)
    if can_compile:
        # Select appropriate tests based on ITP type
        tests = benchmark_data.coq_tests if (itp_type == ITPType.COQ and benchmark_data.coq_tests) else benchmark_data.tests
        unit_test_scores = await metric_generated_code_unit_tests(
            template_engine, content, tests, itp_type=itp_type
        )
    else:
        unit_test_scores = {}
    metric_score = CodeMetricScore(can_compile=can_compile, unit_tests=unit_test_scores)
    metric_score.update_score()
    return metric_score


class LeanSpecFormalScore(BaseModel):
    sound: LeanTestScore
    complete: LeanTestScore


class LeanSpecTestScoreDetail(BaseModel):
    decide: LeanTestScore = LeanTestScore.UNKNOWN
    plausible: LeanTestScore = LeanTestScore.UNKNOWN
    plausible_inverse: LeanTestScore = LeanTestScore.UNKNOWN
    llm: LeanTestScore = LeanTestScore.UNKNOWN
    llm_inverse: LeanTestScore = LeanTestScore.UNKNOWN

    def to_score(self) -> LeanTestScore:
        if self.decide != LeanTestScore.UNKNOWN:
            return self.decide
        if LeanTestScore.FAIL in [self.plausible, self.plausible_inverse]:
            return LeanTestScore.FAIL
        if LeanTestScore.PASS in [self.plausible, self.plausible_inverse]:
            return LeanTestScore.PASS
        assert self.llm != LeanTestScore.FAIL, (
            f"LLM score should not be FAIL: {self.llm}"
        )
        assert self.llm_inverse != LeanTestScore.FAIL, (
            f"LLM inverse score should not be FAIL: {self.llm_inverse}"
        )
        if LeanTestScore.PASS in [self.llm, self.llm_inverse]:
            return LeanTestScore.PASS
        return LeanTestScore.UNKNOWN


class LeanSpecTestScore(BaseModel):
    score: LeanTestScore = LeanTestScore.UNKNOWN

    score_detail: LeanSpecTestScoreDetail = LeanSpecTestScoreDetail()

    def update_score(self):
        self.score = self.score_detail.to_score()


class LeanTestsSummary(BaseModel):
    score: LeanTestScore = LeanTestScore.UNKNOWN
    pass_count: int = 0
    fail_count: int = 0
    unknown_count: int = 0

    def update_score(self):
        if self.fail_count > 0:
            self.score = LeanTestScore.FAIL
        elif self.unknown_count > 0:
            self.score = LeanTestScore.UNKNOWN
        else:
            self.score = LeanTestScore.PASS  # all tests passed or no tests


class SpecMetricScore(MetricScore):
    can_compile: bool
    formal_score: LeanSpecFormalScore

    sound_test_score: LeanTestsSummary = LeanTestsSummary()
    complete_test_score: LeanTestsSummary = LeanTestsSummary()

    sound_tests: Dict[
        int | Tuple[int, int] | str, LeanSpecTestScore
    ] = {}  # str is for seralized tuple
    complete_tests: Dict[int, LeanSpecTestScore] = {}

    def init_test_scores(
        self,
        eval_type: Literal["precond", "postcond"],
        reject_inputs: List[RejectInput],
        test_cases: List[TestCase],
    ):
        if eval_type == "precond":
            for idx in range(len(test_cases)):
                if idx not in self.sound_tests:
                    self.sound_tests[idx] = LeanSpecTestScore()
            for idx in range(len(reject_inputs)):
                if idx not in self.complete_tests:
                    self.complete_tests[idx] = LeanSpecTestScore()
        else:
            for idx in range(len(test_cases)):
                if idx not in self.complete_tests:
                    self.complete_tests[idx] = LeanSpecTestScore()
                for unexpected_idx in range(len(test_cases[idx].unexpected)):
                    if (idx, unexpected_idx) not in self.sound_tests:
                        self.sound_tests[(idx, unexpected_idx)] = LeanSpecTestScore()

    def update_test_scores(self):
        for test_score in self.sound_tests.values():
            test_score.update_score()
        for test_score in self.complete_tests.values():
            test_score.update_score()

    def finalize_test_scores(self):
        for test_score in self.sound_tests.values():
            if test_score.score == LeanTestScore.PASS:
                self.sound_test_score.pass_count += 1
            elif test_score.score == LeanTestScore.FAIL:
                self.sound_test_score.fail_count += 1
            else:
                self.sound_test_score.unknown_count += 1
        for test_score in self.complete_tests.values():
            if test_score.score == LeanTestScore.PASS:
                self.complete_test_score.pass_count += 1
            elif test_score.score == LeanTestScore.FAIL:
                self.complete_test_score.fail_count += 1
            else:
                self.complete_test_score.unknown_count += 1

        self.sound_test_score.update_score()
        self.complete_test_score.update_score()


def _parse_coq_decidable_markers(
    section_msg: str,
    marker_base: str,
    evaluate_type: Literal["precond", "postcond"],
    inverse: bool = False,
) -> Dict[int | Tuple[int, int], str]:
    """Parse Coq Print-based decidable test markers.

    The Print output looks like:
        _m_precond_test_decidable_0 = tt
             : unit
        Goal...Qed. (or Error:...)
        _m_precond_test_decidable_0_inv = tt
             : unit
        Goal ~(...)...
        _m_precond_test_decidable_1 = tt
             : unit
        Goal...

    For postcond sound tests (tuple index):
        _m_postcond_test_decidable_0_1 = tt
             : unit
        _m_postcond_test_decidable_0_1_inv = tt
             : unit

    Args:
        section_msg: The output section to parse (sound or complete)
        marker_base: The base marker name (e.g., "precond_test_decidable")
        evaluate_type: "precond" or "postcond"
        inverse: If True, parse only _inv markers; if False, parse only non-_inv markers
    """
    import re

    result: Dict[int | Tuple[int, int], str] = {}

    # Pattern to match Print marker output: _m_{marker_base}_{idx}[_inv] = tt
    # For postcond sound tests, idx can be "0_1" format (test_idx_unexpected_idx)
    # Capture group 1: the index (e.g., "0" or "0_1")
    # Capture group 2: optional "_inv" suffix
    safe_marker = marker_base.replace("-", "_")
    pattern = rf"_m_{safe_marker}_(\d+(?:_\d+)?)((?:_inv)?)\s*="

    # Find all marker positions
    matches = list(re.finditer(pattern, section_msg))

    for i, match in enumerate(matches):
        idx_str = match.group(1)
        inv_suffix = match.group(2)
        is_inverse_marker = inv_suffix == "_inv"

        # Skip markers that don't match our inverse flag
        if is_inverse_marker != inverse:
            continue

        start_pos = match.end()
        # End position is either the next marker or end of string
        end_pos = matches[i + 1].start() if i + 1 < len(matches) else len(section_msg)

        msg_content = section_msg[start_pos:end_pos]

        # Parse the index
        if "_" in idx_str:
            # Tuple index (e.g., "0_1" -> (0, 1))
            parts = idx_str.split("_")
            idx = (int(parts[0]), int(parts[1]))
        else:
            # Single index
            idx = int(idx_str)

        result[idx] = msg_content

    return result


def update_spec_decidable_scores(
    template_engine: ITPTemplate,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    decidable_msg: str,
    itp_type: ITPType = ITPType.LEAN,
) -> SpecMetricScore:
    # Use ITP-specific markers
    if itp_type == ITPType.COQ:
        markers = ["_marker_test_start", "_marker_sound_decidable_end"]
    else:
        markers = ["###test start###", "###sound decidable end###"]

    # Debug: Log the decidable_msg info
    if itp_type == ITPType.COQ:
        print(f"[DEBUG] update_spec_decidable_scores called for {evaluate_type}")
        print(f"[DEBUG] decidable_msg length: {len(decidable_msg)}")
        print(f"[DEBUG] Looking for markers: {markers}")
        print(f"[DEBUG] Marker 0 found: {markers[0] in decidable_msg}")
        print(f"[DEBUG] Marker 1 found: {markers[1] in decidable_msg}")
        print(f"[DEBUG] decidable_msg repr: {repr(decidable_msg[:2000])}")

    decidable_msg_split = split_message(
        decidable_msg,
        markers,
        remove_first=True,
    )

    if itp_type == ITPType.COQ:
        print(f"[DEBUG] decidable_msg_split length: {len(decidable_msg_split)}")

    if len(decidable_msg_split) != 2:
        if itp_type == ITPType.COQ:
            print(f"[DEBUG] Early return - split didn't produce 2 parts")
        return score
    sound_decidable_msg = decidable_msg_split[0]
    complete_decidable_msg = decidable_msg_split[1]
    sound_decidable_msg_map: Dict[int | Tuple[int, int], str] = {}
    complete_decidable_msg_map: Dict[int, str] = {}

    if evaluate_type == "precond":
        marker = template_engine.PRECOND_TEST_DECIDABLE_MSG_MARKER
    else:
        marker = template_engine.POSTCOND_TEST_DECIDABLE_MSG_MARKER

    # Use different parsing logic for Coq (Print-based markers) vs Lean (XML-like markers)
    if itp_type == ITPType.COQ:
        # Parse Coq Print-based markers - both primary and inverse for bidirectional testing
        sound_decidable_msg_map = _parse_coq_decidable_markers(
            sound_decidable_msg, marker, evaluate_type, inverse=False
        )
        sound_decidable_inv_msg_map = _parse_coq_decidable_markers(
            sound_decidable_msg, marker, evaluate_type, inverse=True
        )
        complete_decidable_msg_map = _parse_coq_decidable_markers(
            complete_decidable_msg, marker, evaluate_type, inverse=False
        )
        complete_decidable_inv_msg_map = _parse_coq_decidable_markers(
            complete_decidable_msg, marker, evaluate_type, inverse=True
        )

        print(f"[DEBUG] Parsing Coq decidable markers for {evaluate_type}")
        print(f"[DEBUG] Sound primary results: {list(sound_decidable_msg_map.keys())}")
        print(f"[DEBUG] Sound inverse results: {list(sound_decidable_inv_msg_map.keys())}")
        print(f"[DEBUG] Complete primary results: {list(complete_decidable_msg_map.keys())}")
        print(f"[DEBUG] Complete inverse results: {list(complete_decidable_inv_msg_map.keys())}")

        # Bidirectional scoring for sound tests using SOLVED/UNSOLVED markers
        # Note: Check UNSOLVED first since "UNSOLVED" contains "SOLVED" as substring
        for idx, msg in sound_decidable_msg_map.items():
            if idx not in score.sound_tests:
                continue
            # Check for UNSOLVED first (since UNSOLVED contains SOLVED as substring)
            primary_solved = template_engine.UNSOLVED_MARKER not in msg and template_engine.SOLVED_MARKER in msg
            inv_msg = sound_decidable_inv_msg_map.get(idx, "")
            inverse_solved = template_engine.UNSOLVED_MARKER not in inv_msg and template_engine.SOLVED_MARKER in inv_msg

            if primary_solved:
                decide_score = LeanTestScore.PASS
            elif inverse_solved:
                # Primary failed but inverse succeeded -> spec is wrong
                decide_score = LeanTestScore.FAIL
            else:
                # Both failed -> unknown
                decide_score = LeanTestScore.UNKNOWN

            print(f"[DEBUG] Sound test {idx}: primary_solved={primary_solved}, inverse_solved={inverse_solved} -> {decide_score}")
            score.sound_tests[idx].score_detail.decide = decide_score

        # Bidirectional scoring for complete tests using SOLVED/UNSOLVED markers
        for idx, msg in complete_decidable_msg_map.items():
            if idx not in score.complete_tests:
                continue
            # Check for UNSOLVED first (since UNSOLVED contains SOLVED as substring)
            primary_solved = template_engine.UNSOLVED_MARKER not in msg and template_engine.SOLVED_MARKER in msg
            inv_msg = complete_decidable_inv_msg_map.get(idx, "")
            inverse_solved = template_engine.UNSOLVED_MARKER not in inv_msg and template_engine.SOLVED_MARKER in inv_msg

            if primary_solved:
                decide_score = LeanTestScore.PASS
            elif inverse_solved:
                # Primary failed but inverse succeeded -> spec is wrong
                decide_score = LeanTestScore.FAIL
            else:
                # Both failed -> unknown
                decide_score = LeanTestScore.UNKNOWN

            print(f"[DEBUG] Complete test {idx}: primary_solved={primary_solved}, inverse_solved={inverse_solved} -> {decide_score}")
            score.complete_tests[idx].score_detail.decide = decide_score

    else:
        # Parse Lean XML-like markers
        spec_decidable_start_marker = f"<{marker}>"
        spec_decidable_end_marker = f"</{marker}>"
        sound_decidable_msg_parts = sound_decidable_msg.split(spec_decidable_start_marker)[1:]
        complete_decidable_msg_parts = complete_decidable_msg.split(spec_decidable_start_marker)[
            1:
        ]

        for msg in sound_decidable_msg_parts:
            msg = msg.split(spec_decidable_end_marker)
            assert len(msg) == 2, f"Decidable msg should be split into 2 parts: {msg}"
            if evaluate_type == "precond":
                sound_decidable_msg_map[int(msg[0])] = msg[1]
            else:
                idxs = msg[0].split(",")
                assert len(idxs) == 2, (
                    f"Decidable msg idx should be split into 2 parts: {msg}"
                )
                sound_decidable_msg_map[(int(idxs[0]), int(idxs[1]))] = msg[1]
        for msg in complete_decidable_msg_parts:
            msg = msg.split(spec_decidable_end_marker)
            assert len(msg) == 2, f"Decidable msg should be split into 2 parts: {msg}"
            complete_decidable_msg_map[int(msg[0])] = msg[1]

        # Lean scoring (unchanged - no bidirectional testing)
        for idx, msg in sound_decidable_msg_map.items():
            if idx not in score.sound_tests:
                continue
            if template_engine.DECIDABLE_ERR_MSG in msg:
                decide_score = LeanTestScore.FAIL
            elif "error" in msg.lower():
                decide_score = LeanTestScore.UNKNOWN
            else:
                decide_score = LeanTestScore.PASS
            score.sound_tests[idx].score_detail.decide = decide_score

        for idx, msg in complete_decidable_msg_map.items():
            if idx not in score.complete_tests:
                continue
            if template_engine.DECIDABLE_ERR_MSG in msg:
                decide_score = LeanTestScore.FAIL
            elif "error" in msg.lower():
                decide_score = LeanTestScore.UNKNOWN
            else:
                decide_score = LeanTestScore.PASS
            score.complete_tests[idx].score_detail.decide = decide_score

    score.update_test_scores()
    return score


def _parse_coq_quickchick_results(output: str) -> List[str]:
    """Parse Coq QuickChick output into a list of 'pass' or 'fail' results."""
    results = []
    for line in output.split('\n'):
        if '+++ Passed' in line:
            results.append('pass')
        elif '*** Failed' in line:
            results.append('fail')
    return results


def _update_spec_plausible_scores_coq(
    template_engine: ITPTemplate,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    plausible_msg: str,
    use_plausible_pass: bool,
) -> SpecMetricScore:
    """Parse Coq QuickChick output sequentially for plausible tests.

    Since Coq comments don't appear in output, we parse by splitting on
    section markers and counting QuickChick results in each section.
    """
    markers = [
        "_marker_test_start",
        "_marker_sound_plausible_end",
        "_marker_sound_plausible_inverse_end",
        "_marker_complete_plausible_end",
    ]
    plausible_msg_split = split_message(
        plausible_msg,
        markers,
        remove_first=True,
    )
    if len(plausible_msg_split) != 4:
        return score

    sound_section = plausible_msg_split[0]
    sound_inverse_section = plausible_msg_split[1]
    complete_section = plausible_msg_split[2]
    complete_inverse_section = plausible_msg_split[3]

    # Parse QuickChick results from each section
    sound_results = _parse_coq_quickchick_results(sound_section)
    sound_inverse_results = _parse_coq_quickchick_results(sound_inverse_section)
    complete_results = _parse_coq_quickchick_results(complete_section)
    complete_inverse_results = _parse_coq_quickchick_results(complete_inverse_section)

    # Get test indices from score
    sound_test_keys = list(score.sound_tests.keys())
    complete_test_keys = list(score.complete_tests.keys())

    # Map results to tests by position
    for i, key in enumerate(sound_test_keys):
        if i < len(sound_results):
            result = sound_results[i]
            if result == 'pass':
                score.sound_tests[key].score_detail["plausible"] = LeanTestScore.PASS
            else:
                score.sound_tests[key].score_detail["plausible"] = LeanTestScore.FAIL
        if i < len(sound_inverse_results):
            result = sound_inverse_results[i]
            if result == 'pass':
                # Inverse test passing means the original property doesn't hold
                score.sound_tests[key].score_detail["plausible_inverse"] = LeanTestScore.PASS
            else:
                score.sound_tests[key].score_detail["plausible_inverse"] = LeanTestScore.FAIL

    for i, key in enumerate(complete_test_keys):
        if i < len(complete_results):
            result = complete_results[i]
            if result == 'pass':
                score.complete_tests[key].score_detail["plausible"] = LeanTestScore.PASS
            else:
                score.complete_tests[key].score_detail["plausible"] = LeanTestScore.FAIL
        if i < len(complete_inverse_results):
            result = complete_inverse_results[i]
            if result == 'pass':
                score.complete_tests[key].score_detail["plausible_inverse"] = LeanTestScore.PASS
            else:
                score.complete_tests[key].score_detail["plausible_inverse"] = LeanTestScore.FAIL

    # Finalize scores based on plausible results
    for key in sound_test_keys:
        detail = score.sound_tests[key].score_detail
        if use_plausible_pass:
            # Sound test passes if plausible=pass OR (plausible_inverse=fail when precond holds)
            if detail.get("plausible") == LeanTestScore.PASS:
                score.sound_tests[key].score = LeanTestScore.PASS
            elif detail.get("plausible_inverse") == LeanTestScore.FAIL:
                score.sound_tests[key].score = LeanTestScore.PASS
            elif detail.get("plausible") == LeanTestScore.FAIL or detail.get("plausible_inverse") == LeanTestScore.PASS:
                score.sound_tests[key].score = LeanTestScore.FAIL

    for key in complete_test_keys:
        detail = score.complete_tests[key].score_detail
        if use_plausible_pass:
            if detail.get("plausible") == LeanTestScore.PASS:
                score.complete_tests[key].score = LeanTestScore.PASS
            elif detail.get("plausible_inverse") == LeanTestScore.FAIL:
                score.complete_tests[key].score = LeanTestScore.PASS
            elif detail.get("plausible") == LeanTestScore.FAIL or detail.get("plausible_inverse") == LeanTestScore.PASS:
                score.complete_tests[key].score = LeanTestScore.FAIL

    score.update_test_scores()
    return score


def _parse_coq_print_markers(
    section_msg: str,
    marker_base: str,
    evaluate_type: Literal["precond", "postcond"],
    is_sound: bool,
    is_inverse: bool = False,
) -> Dict[int | Tuple[int, int], str]:
    """Parse Coq Print-based test markers and extract test messages.

    The Print output looks like:
        _m_postcond_test_undecidable_plausible_0_0_s = tt
             : unit
        QuickChick (...)
        +++ Passed 10000 tests

    We need to find markers like `_m_{marker_base}_{idx}_{suffix}` where suffix is:
    - _s for sound tests
    - _s_inv for sound inverse tests
    - _c for complete tests
    - _c_inv for complete inverse tests

    Args:
        section_msg: The output section to parse
        marker_base: The base marker name (e.g., "postcond_test_undecidable_plausible")
        evaluate_type: "precond" or "postcond"
        is_sound: True for sound tests, False for complete tests
        is_inverse: True for inverse tests
    """
    import re

    result: Dict[int | Tuple[int, int], str] = {}

    # Determine suffix based on is_sound and is_inverse
    if is_sound:
        suffix = "_s_inv" if is_inverse else "_s"
    else:
        suffix = "_c_inv" if is_inverse else "_c"

    # Pattern to match Print marker output: _m_{marker_base}_{idx}{suffix} = tt
    # The idx can be single number (e.g., "0") or double (e.g., "0_0" for postcond sound tests)
    safe_marker = marker_base.replace("-", "_")
    pattern = rf"_m_{safe_marker}_(\d+(?:_\d+)?){suffix}\s*="

    # Find all marker positions
    matches = list(re.finditer(pattern, section_msg))

    for i, match in enumerate(matches):
        idx_str = match.group(1)
        start_pos = match.end()
        # End position is either the next marker or end of string
        end_pos = matches[i + 1].start() if i + 1 < len(matches) else len(section_msg)

        msg_content = section_msg[start_pos:end_pos]

        # Parse the index
        if "_" in idx_str:
            # Tuple index (e.g., "0_0" -> (0, 0))
            parts = idx_str.split("_")
            idx = (int(parts[0]), int(parts[1]))
        else:
            # Single index
            idx = int(idx_str)

        result[idx] = msg_content

    return result


def update_spec_plausible_scores(
    template_engine: ITPTemplate,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    plausible_msg: str,
    use_plausible_pass: bool,
    itp_type: ITPType = ITPType.LEAN,
) -> SpecMetricScore:
    # Use ITP-specific markers
    if itp_type == ITPType.COQ:
        markers = [
            "_marker_test_start",
            "_marker_sound_plausible_end",
            "_marker_sound_plausible_inverse_end",
            "_marker_complete_plausible_end",
        ]
    else:
        markers = [
            "###test start###",
            "###sound plausible end###",
            "###sound plausible inverse end###",
            "###complete plausible end###",
        ]
    plausible_msg_split = split_message(
        plausible_msg,
        markers,
        remove_first=True,
    )
    if len(plausible_msg_split) != 4:
        return score
    sound_plausible_msg = plausible_msg_split[0]
    sound_plausible_inverse_msg = plausible_msg_split[1]
    complete_plausible_msg = plausible_msg_split[2]
    complete_plausible_inverse_msg = plausible_msg_split[3]

    sound_plausible_msg_map: Dict[int | Tuple[int, int], str] = {}
    sound_plausible_inverse_msg_map: Dict[int | Tuple[int, int], str] = {}
    complete_plausible_msg_map: Dict[int, str] = {}
    complete_plausible_inverse_msg_map: Dict[int, str] = {}

    if evaluate_type == "precond":
        marker_func = template_engine.PRECOND_TEST_UNDECIDABLE_MSG_MARKER
    else:
        marker_func = template_engine.POSTCOND_TEST_UNDECIDABLE_MSG_MARKER

    marker_base = marker_func(template_engine.UNDECIDABLE_PLAUSIBLE)

    # Use different parsing logic for Coq (Print-based markers) vs Lean (XML-like markers)
    if itp_type == ITPType.COQ:
        # Parse Coq Print-based markers
        # Sound tests: normal (no _inv suffix)
        sound_plausible_msg_map = _parse_coq_print_markers(
            sound_plausible_msg, marker_base, evaluate_type, is_sound=True, is_inverse=False
        )
        # Sound inverse tests: have _inv suffix
        sound_plausible_inverse_msg_map = _parse_coq_print_markers(
            sound_plausible_inverse_msg, marker_base, evaluate_type, is_sound=True, is_inverse=True
        )
        # Complete tests: normal (no _inv suffix)
        complete_plausible_msg_map = _parse_coq_print_markers(
            complete_plausible_msg, marker_base, evaluate_type, is_sound=False, is_inverse=False
        )
        # Complete inverse tests: have _inv suffix
        complete_plausible_inverse_msg_map = _parse_coq_print_markers(
            complete_plausible_inverse_msg, marker_base, evaluate_type, is_sound=False, is_inverse=True
        )
    else:
        # Parse Lean XML-like markers
        spec_undecidable_start_marker = f"<{marker_base}>"
        spec_undecidable_end_marker = f"</{marker_base}>"
        sound_plausible_msgs = sound_plausible_msg.split(spec_undecidable_start_marker)[1:]
        sound_plausible_inverse_msgs = sound_plausible_inverse_msg.split(
            spec_undecidable_start_marker
        )[1:]
        complete_plausible_msgs = complete_plausible_msg.split(
            spec_undecidable_start_marker
        )[1:]
        complete_plausible_inverse_msgs = complete_plausible_inverse_msg.split(
            spec_undecidable_start_marker
        )[1:]

        for msg in complete_plausible_msgs:
            msg = msg.split(spec_undecidable_end_marker)
            assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
            complete_plausible_msg_map[int(msg[0])] = msg[1]
        for msg in complete_plausible_inverse_msgs:
            msg = msg.split(spec_undecidable_end_marker)
            assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
            complete_plausible_inverse_msg_map[int(msg[0])] = msg[1]
        for msg in sound_plausible_msgs:
            msg = msg.split(spec_undecidable_end_marker)
            assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
            if evaluate_type == "precond":
                sound_plausible_msg_map[int(msg[0])] = msg[1]
            else:
                idxs = msg[0].split(",")
                assert len(idxs) == 2, (
                    f"Undecidable msg idx should be split into 2 parts: {msg}"
                )
                sound_plausible_msg_map[(int(idxs[0]), int(idxs[1]))] = msg[1]
        for msg in sound_plausible_inverse_msgs:
            msg = msg.split(spec_undecidable_end_marker)
            assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
            if evaluate_type == "precond":
                sound_plausible_inverse_msg_map[int(msg[0])] = msg[1]
            else:
                idxs = msg[0].split(",")
                assert len(idxs) == 2, (
                    f"Undecidable msg idx should be split into 2 parts: {msg}"
                )
                sound_plausible_inverse_msg_map[(int(idxs[0]), int(idxs[1]))] = msg[1]

    def plausible_msg_to_score(msg: str, inverse: bool) -> LeanTestScore:
        score = LeanTestScore.UNKNOWN

        if itp_type == ITPType.COQ:
            # For Coq with auto tactics: no error = success, error = fail
            # Check for common error patterns in Coq output
            error_patterns = ["Error:", "error:", "Tactic failure", "Cannot find"]
            has_error = any(pattern in msg for pattern in error_patterns)

            if has_error:
                score = LeanTestScore.FAIL
            elif msg.strip():  # Non-empty message without error = success
                if use_plausible_pass:
                    score = LeanTestScore.PASS
                else:
                    score = LeanTestScore.UNKNOWN
        else:
            # For Lean: use QuickChick/Plausible success/fail messages
            if template_engine.PLAUSIBLE_FAILED_MSG in msg:
                score = LeanTestScore.FAIL
            elif (
                template_engine.PLAUSIBLE_SUCCESS_MSG in msg
                or template_engine.SIMP_SUCCESS_MSG in msg
            ):
                if use_plausible_pass:
                    score = LeanTestScore.PASS
                else:
                    score = LeanTestScore.UNKNOWN

        if inverse:
            if score == LeanTestScore.PASS:
                score = (
                    LeanTestScore.UNKNOWN
                )  # if no counter example, we don't know if it holds
            elif score == LeanTestScore.FAIL:
                score = LeanTestScore.PASS
        return score

    for idx, msg in complete_plausible_msg_map.items():
        score.complete_tests[idx].score_detail.plausible = plausible_msg_to_score(
            msg, inverse=False
        )
    for idx, msg in complete_plausible_inverse_msg_map.items():
        score.complete_tests[
            idx
        ].score_detail.plausible_inverse = plausible_msg_to_score(msg, inverse=True)
    for idx, msg in sound_plausible_msg_map.items():
        score.sound_tests[idx].score_detail.plausible = plausible_msg_to_score(
            msg, inverse=False
        )
    for idx, msg in sound_plausible_inverse_msg_map.items():
        score.sound_tests[idx].score_detail.plausible_inverse = plausible_msg_to_score(
            msg, inverse=True
        )

    score.update_test_scores()
    return score


# TODO: precond and postcond name
async def metric_generated_spec_unit_tests(
    config: BenchmarkSpecEvaluationConfig,
    template_engine: ITPTemplate,
    generated_spec_content: str,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    reject_inputs: List[RejectInput],
    test_cases: List[TestCase],
    precond_name: str = "",
    postcond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> SpecMetricScore:
    score.init_test_scores(evaluate_type, reject_inputs, test_cases)

    content_header = (
        template_engine.render_test_imports() + "\n" + generated_spec_content
    )

    # Print markers differ between ITPs
    if itp_type == ITPType.COQ:
        # Use Print with defined constants to output markers - Coq comments don't appear in output
        # Define marker constants first, then print them
        test_start_marker = '\nDefinition _marker_test_start := tt. Print _marker_test_start.\n\n'
        sound_decidable_end_marker = '\nDefinition _marker_sound_decidable_end := tt. Print _marker_sound_decidable_end.\n\n'
        sound_plausible_end_marker = '\nDefinition _marker_sound_plausible_end := tt. Print _marker_sound_plausible_end.\n\n'
        sound_plausible_inv_end_marker = '\nDefinition _marker_sound_plausible_inverse_end := tt. Print _marker_sound_plausible_inverse_end.\n\n'
        complete_plausible_end_marker = '\nDefinition _marker_complete_plausible_end := tt. Print _marker_complete_plausible_end.\n\n'
    else:
        test_start_marker = '\n#print "###test start###"\n\n'
        sound_decidable_end_marker = '\n#print "###sound decidable end###"\n\n'
        sound_plausible_end_marker = '\n#print "###sound plausible end###"\n\n'
        sound_plausible_inv_end_marker = '\n#print "###sound plausible inverse end###"\n\n'
        complete_plausible_end_marker = '\n#print "###complete plausible end###"\n\n'

    content_header += test_start_marker

    # Decidable tests

    decidable_content = content_header

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_sound_decidable(
                        test_case, test_idx=idx
                    )
                )
        else:
            for unexpected_idx in range(len(test_case.unexpected)):
                if (
                    score.sound_tests[(idx, unexpected_idx)].score
                    == LeanTestScore.UNKNOWN
                ):
                    decidable_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_decidable(
                            test_case, test_idx=idx, unexpected_idx=unexpected_idx
                        )
                    )

    decidable_content += sound_decidable_end_marker

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_complete_decidable(
                        reject_input, test_idx=idx
                    )
                )
    else:
        for idx, test_case in enumerate(test_cases):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_decidable(
                        test_case, test_idx=idx
                    )
                )

    _, decidable_msg = await metric_itp_compile(itp_type, decidable_content)
    if decidable_msg != "TIMEOUT" and "COMPERROR" not in decidable_msg:
        score = update_spec_decidable_scores(
            template_engine, score, evaluate_type, decidable_msg, itp_type
        )
    else:
        print(f"ITP compile failed for decidable tests: {decidable_msg}")

    # Skip plausible tests for Coq - auto tactics are used in decidable tests
    # Plausible (PBT) only makes sense for Lean where we have #check_plausible
    if itp_type == ITPType.COQ:
        score.finalize_test_scores()
        return score

    # Plausible tests (Lean only)

    plausible_content = content_header

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_sound_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=False,
                        use_grind=config.use_grind,
                    )
                )
        else:
            for unexpected_idx in range(len(test_case.unexpected)):
                if (
                    score.sound_tests[(idx, unexpected_idx)].score
                    == LeanTestScore.UNKNOWN
                ):
                    plausible_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_plausible(
                            test_case,
                            test_idx=idx,
                            unexpected_idx=unexpected_idx,
                            inverse=False,
                            use_grind=config.use_grind,
                        )
                    )

    plausible_content += sound_plausible_end_marker

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_sound_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=True,
                        use_grind=config.use_grind,
                    )
                )
        else:
            for unexpected_idx in range(len(test_case.unexpected)):
                if (
                    score.sound_tests[(idx, unexpected_idx)].score
                    == LeanTestScore.UNKNOWN
                ):
                    plausible_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_plausible(
                            test_case,
                            test_idx=idx,
                            unexpected_idx=unexpected_idx,
                            inverse=True,
                            use_grind=config.use_grind,
                        )
                    )

    plausible_content += sound_plausible_inv_end_marker

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_complete_plausible(
                        reject_input,
                        test_idx=idx,
                        inverse=False,
                        use_grind=config.use_grind,
                    )
                )
    else:
        for idx, test_case in enumerate(test_cases):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=False,
                        use_grind=config.use_grind,
                    )
                )

    plausible_content += complete_plausible_end_marker

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_complete_plausible(
                        reject_input,
                        test_idx=idx,
                        inverse=True,
                        use_grind=config.use_grind,
                    )
                )
    else:
        for idx, test_case in enumerate(test_cases):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=True,
                        use_grind=config.use_grind,
                    )
                )

    _, plausible_msg = await metric_itp_compile(itp_type, plausible_content)
    if plausible_msg != "TIMEOUT" and "COMPERROR" not in plausible_msg:
        score = update_spec_plausible_scores(
            template_engine,
            score,
            evaluate_type,
            plausible_msg,
            config.use_plausible_pass,
            itp_type,
        )
    else:
        print(f"ITP compile failed for plausible tests: {plausible_msg}")

    score.finalize_test_scores()
    return score


def make_spec_aux_testable(spec_aux: str) -> str:
    """
    Make the spec_aux testable by adding @[reducible, simp] to all definitions if they are not already there.
    """
    lines = spec_aux.split("\n")
    for i, line in enumerate(lines):
        if line.startswith("def "):
            if "@[reducible, simp]" not in line and (
                i == 0 or "@[reducible, simp]" not in lines[i - 1]
            ):
                lines[i] = line.replace("def ", "@[reducible, simp] def ")
    return "\n".join(lines)


def make_spec_test_content(
    template_engine: ITPTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> str:
    # Select appropriate data based on ITP type
    if itp_type == ITPType.COQ:
        itp_data = benchmark_data.coq_data
    else:
        itp_data = benchmark_data.lean_data

    content = (
        template_engine.render_imports(itp_data.task_imports, "task")
        + "\n"
    )
    content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    content += (
        template_engine.render_aux(itp_data.task_aux, "task") + "\n"
    )

    content += (
        template_engine.render_aux(
            make_spec_aux_testable(artifact.precond_aux), "precond"
        )
        + "\n"
    )
    content += (
        template_engine.render_precond(artifact.precond, precond_name=precond_name)
        + "\n"
    )

    if evaluate_type == "postcond":
        content += (
            template_engine.render_aux(
                make_spec_aux_testable(artifact.postcond_aux), "postcond"
            )
            + "\n"
        )
        content += (
            template_engine.render_postcond(
                artifact.postcond,
                precond_name=precond_name,
                postcond_name=postcond_name,
            )
            + "\n"
        )

    return content


async def metric_generated_spec_compile(
    existing_score: Optional[SpecMetricScore],
    template_engine: ITPTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> SpecMetricScore:
    if existing_score is not None:
        return existing_score

    content = make_spec_test_content(
        template_engine,
        benchmark_data,
        artifact,
        evaluate_type,
        precond_name=precond_name,
        postcond_name=postcond_name,
        itp_type=itp_type,
    )

    can_compile, compile_err = await metric_itp_compile(itp_type, content)

    return SpecMetricScore(
        can_compile=can_compile,
        formal_score=LeanSpecFormalScore(
            sound=LeanTestScore.UNKNOWN, complete=LeanTestScore.UNKNOWN
        ),
        sound_tests={},
        complete_tests={},
    )


# Only do compile test and unit test for precond and postcond
# formal proving and unit test with proof will be done in a separate pass
# TODO rename to metric_generated_spec_unit_tests
async def metric_generated_spec_unit_test_entry(
    existing_score: SpecMetricScore,
    config: BenchmarkSpecEvaluationConfig,
    template_engine: ITPTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> SpecMetricScore:
    score = existing_score

    content = make_spec_test_content(
        template_engine,
        benchmark_data,
        artifact,
        evaluate_type,
        precond_name=precond_name,
        postcond_name=postcond_name,
        itp_type=itp_type,
    )

    if score.can_compile:
        if config.unit_test:
            # Select appropriate tests based on ITP type
            tests = benchmark_data.coq_tests if (itp_type == ITPType.COQ and benchmark_data.coq_tests) else benchmark_data.tests
            score = await metric_generated_spec_unit_tests(
                config,
                template_engine,
                content,
                score,
                evaluate_type,
                benchmark_data.reject_inputs,
                tests,
                precond_name,
                postcond_name,
                itp_type=itp_type,
            )

    return score


class ProofMetricScore(MetricScore):
    can_compile: bool
    error: Optional[str] = None


async def metric_generated_proof(
    template_engine: ITPTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    precond_name: str = "",
    postcond_name: str = "",
    itp_type: ITPType = ITPType.LEAN,
) -> ProofMetricScore:
    # Get cheat codes from template
    cheat_codes = template_engine.get_cheat_codes()
    for code in cheat_codes:
        if code in artifact.proof_aux or code in artifact.proof:
            return ProofMetricScore(
                can_compile=False,
                error="cheatcodes like `sorry` or `admit` should not be used in proof",
            )

    # Select appropriate data based on ITP type
    if itp_type == ITPType.COQ:
        itp_data = benchmark_data.coq_data
    else:
        itp_data = benchmark_data.lean_data

    content = (
        template_engine.render_imports(itp_data.task_imports, "task")
        + "\n"
    )
    content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    content += (
        template_engine.render_aux(itp_data.task_aux, "task") + "\n"
    )

    content += template_engine.render_aux(artifact.precond_aux, "precond") + "\n"
    content += (
        template_engine.render_precond(artifact.precond, precond_name=precond_name)
        + "\n"
    )

    content += template_engine.render_aux(artifact.code_aux, "code") + "\n"
    content += (
        template_engine.render_code(artifact.code, precond_name=precond_name) + "\n"
    )

    content += template_engine.render_aux(artifact.postcond_aux, "postcond") + "\n"
    content += (
        template_engine.render_postcond(
            artifact.postcond, precond_name=precond_name, postcond_name=postcond_name
        )
        + "\n"
    )

    content += template_engine.render_aux(artifact.proof_aux, "proof") + "\n"
    content += (
        template_engine.render_proof(
            artifact.proof, precond_name=precond_name, postcond_name=postcond_name
        )
        + "\n"
    )

    can_compile, compile_err = await metric_itp_compile(itp_type, content)
    return ProofMetricScore(can_compile=can_compile, error=compile_err)
