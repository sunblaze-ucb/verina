from enum import Enum
from typing import Dict, List, Literal, Optional, Tuple
from uuid import uuid4

from prefect import task
from prefect.cache_policies import INPUTS, TASK_SOURCE
from pydantic import BaseModel

from verina.benchmark.common import BenchmarkSpecEvaluationConfig
from verina.benchmark.report import EvaluationTaskArtifact
from verina.dataset.schema import BenchmarkData, RejectInput, TestCase
from verina.dataset.template import LeanGenerationTaskTemplate
from verina.lean import (
    check_lean_compile,
    create_lean_file,
)


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
    timeout_seconds=200,
)
async def metric_lean_compile(
    lean_content: str, file_name: Optional[str] = None
) -> Tuple[bool, str]:
    """
    Check if the generated Lean code compiles.
    """
    if file_name is None:
        file_name = str(uuid4())
    lean_file = create_lean_file(file_name, lean_content)
    return check_lean_compile(lean_file)


class LeanTestScore(Enum):
    PASS = "pass"
    FAIL = "fail"
    UNKNOWN = "unknown"


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
    template_engine: LeanGenerationTaskTemplate,
    generated_code_lean_content: str,
    test_cases: List[TestCase],
) -> Dict[int, LeanTestScore]:
    lean_content = (
        template_engine.render_test_imports() + "\n" + generated_code_lean_content
    )

    for idx, test_case in enumerate(test_cases):
        lean_content += "\n\n" + template_engine.render_code_unit_test(
            test_case, test_idx=idx
        )

    can_compile, compile_msg = await metric_lean_compile(lean_content)

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
        if template_engine.DECIDABLE_ERR_MSG in msg:
            scores[idx] = LeanTestScore.FAIL
        elif "error" in msg:
            # should not happen -- code should always be evaluable
            scores[idx] = LeanTestScore.UNKNOWN
        else:
            scores[idx] = LeanTestScore.PASS

    return scores


async def metric_generated_code(
    template_engine: LeanGenerationTaskTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    precond_name: str = "",
) -> CodeMetricScore:
    lean_content = (
        template_engine.render_imports(benchmark_data.lean_data.task_imports, "task")
        + "\n"
    )
    lean_content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    lean_content += (
        template_engine.render_aux(benchmark_data.lean_data.task_aux, "task") + "\n"
    )

    lean_content += template_engine.render_aux(artifact.precond_aux, "precond") + "\n"
    precond = artifact.precond
    if precond == "":
        precond = "True -- no precondition"
    lean_content += (
        template_engine.render_precond(precond, precond_name=precond_name) + "\n"
    )

    lean_content += template_engine.render_aux(artifact.code_aux, "code") + "\n"
    lean_content += (
        template_engine.render_code(artifact.code, precond_name=precond_name) + "\n"
    )

    can_compile, compile_err = await metric_lean_compile(lean_content)
    if can_compile:
        unit_test_scores = await metric_generated_code_unit_tests(
            template_engine, lean_content, benchmark_data.tests
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


def update_spec_decidable_scores(
    template_engine: LeanGenerationTaskTemplate,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    decidable_msg: str,
) -> SpecMetricScore:
    decidable_msg_split = split_message(
        decidable_msg,
        ["###test start###", "###sound decidable end###"],
        remove_first=True,
    )
    if len(decidable_msg_split) != 2:
        return score
    sound_decidable_msg = decidable_msg_split[0]
    complete_decidable_msg = decidable_msg_split[1]
    sound_decidable_msg_map: Dict[int | Tuple[int, int], str] = {}
    complete_decidable_msg_map: Dict[int, str] = {}

    if evaluate_type == "precond":
        marker = template_engine.PRECOND_TEST_DECIDABLE_MSG_MARKER
    else:
        marker = template_engine.POSTCOND_TEST_DECIDABLE_MSG_MARKER

    spec_decidable_start_marker = f"<{marker}>"
    spec_decidable_end_marker = f"</{marker}>"
    sound_decidable_msg = sound_decidable_msg.split(spec_decidable_start_marker)[1:]
    complete_decidable_msg = complete_decidable_msg.split(spec_decidable_start_marker)[
        1:
    ]

    for msg in sound_decidable_msg:
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
    for msg in complete_decidable_msg:
        msg = msg.split(spec_decidable_end_marker)
        assert len(msg) == 2, f"Decidable msg should be split into 2 parts: {msg}"
        complete_decidable_msg_map[int(msg[0])] = msg[1]

    for idx, msg in sound_decidable_msg_map.items():
        if template_engine.DECIDABLE_ERR_MSG in msg:
            decide_score = LeanTestScore.FAIL
        elif "error" in msg:
            decide_score = LeanTestScore.UNKNOWN
        else:
            decide_score = LeanTestScore.PASS
        score.sound_tests[idx].score_detail.decide = decide_score

    for idx, msg in complete_decidable_msg_map.items():
        if template_engine.DECIDABLE_ERR_MSG in msg:
            decide_score = LeanTestScore.FAIL
        elif "error" in msg:
            decide_score = LeanTestScore.UNKNOWN
        else:
            decide_score = LeanTestScore.PASS
        score.complete_tests[idx].score_detail.decide = decide_score

    score.update_test_scores()
    return score


def update_spec_plausible_scores(
    template_engine: LeanGenerationTaskTemplate,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    plausible_msg: str,
    use_plausible_pass: bool,
) -> SpecMetricScore:
    plausible_msg_split = split_message(
        plausible_msg,
        [
            "###test start###",
            "###sound plausible end###",
            "###sound plausible inverse end###",
            "###complete plausible end###",
        ],
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

    spec_undecidable_start_marker = (
        f"<{marker_func(template_engine.UNDECIDABLE_PLAUSIBLE)}>"
    )
    spec_undecidable_end_marker = (
        f"</{marker_func(template_engine.UNDECIDABLE_PLAUSIBLE)}>"
    )
    sound_plausible_msg = sound_plausible_msg.split(spec_undecidable_start_marker)[1:]
    sound_plausible_inverse_msg = sound_plausible_inverse_msg.split(
        spec_undecidable_start_marker
    )[1:]
    complete_plausible_msg = complete_plausible_msg.split(
        spec_undecidable_start_marker
    )[1:]
    complete_plausible_inverse_msg = complete_plausible_inverse_msg.split(
        spec_undecidable_start_marker
    )[1:]

    for msg in complete_plausible_msg:
        msg = msg.split(spec_undecidable_end_marker)
        assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
        complete_plausible_msg_map[int(msg[0])] = msg[1]
    for msg in complete_plausible_inverse_msg:
        msg = msg.split(spec_undecidable_end_marker)
        assert len(msg) == 2, f"Undecidable msg should be split into 2 parts: {msg}"
        complete_plausible_inverse_msg_map[int(msg[0])] = msg[1]
    for msg in sound_plausible_msg:
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
    for msg in sound_plausible_inverse_msg:
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
    template_engine: LeanGenerationTaskTemplate,
    generated_spec_lean_content: str,
    score: SpecMetricScore,
    evaluate_type: Literal["precond", "postcond"],
    reject_inputs: List[RejectInput],
    test_cases: List[TestCase],
    precond_name: str = "",
    postcond_name: str = "",
) -> SpecMetricScore:
    score.init_test_scores(evaluate_type, reject_inputs, test_cases)

    lean_content_header = (
        template_engine.render_test_imports() + "\n" + generated_spec_lean_content
    )

    lean_content_header += '\n#print "###test start###"\n\n'

    # Decidable tests

    decidable_lean_content = lean_content_header

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_lean_content += (
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
                    decidable_lean_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_decidable(
                            test_case, test_idx=idx, unexpected_idx=unexpected_idx
                        )
                    )

    decidable_lean_content += '\n#print "###sound decidable end###"\n\n'

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_lean_content += (
                    "\n\n"
                    + template_engine.render_precond_unit_test_complete_decidable(
                        reject_input, test_idx=idx
                    )
                )
    else:
        for idx, test_case in enumerate(test_cases):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                decidable_lean_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_decidable(
                        test_case, test_idx=idx
                    )
                )

    _, decidable_msg = await metric_lean_compile(decidable_lean_content)
    if decidable_msg != "TIMEOUT" and "COMPERROR" not in decidable_msg:
        score = update_spec_decidable_scores(
            template_engine, score, evaluate_type, decidable_msg
        )
    else:
        print(f"Lean compile failed for decidable tests: {decidable_msg}")

    # Plausible tests

    plausible_lean_content = lean_content_header

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_lean_content += (
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
                    plausible_lean_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_plausible(
                            test_case,
                            test_idx=idx,
                            unexpected_idx=unexpected_idx,
                            inverse=False,
                            use_grind=config.use_grind,
                        )
                    )

    plausible_lean_content += '\n#print "###sound plausible end###"\n\n'

    for idx, test_case in enumerate(test_cases):
        if evaluate_type == "precond":
            if score.sound_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_lean_content += (
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
                    plausible_lean_content += (
                        "\n\n"
                        + template_engine.render_postcond_unit_test_sound_plausible(
                            test_case,
                            test_idx=idx,
                            unexpected_idx=unexpected_idx,
                            inverse=True,
                            use_grind=config.use_grind,
                        )
                    )

    plausible_lean_content += '\n#print "###sound plausible inverse end###"\n\n'

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_lean_content += (
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
                plausible_lean_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=False,
                        use_grind=config.use_grind,
                    )
                )

    plausible_lean_content += '\n#print "###complete plausible end###"\n\n'

    if evaluate_type == "precond":
        for idx, reject_input in enumerate(reject_inputs):
            if score.complete_tests[idx].score == LeanTestScore.UNKNOWN:
                plausible_lean_content += (
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
                plausible_lean_content += (
                    "\n\n"
                    + template_engine.render_postcond_unit_test_complete_plausible(
                        test_case,
                        test_idx=idx,
                        inverse=True,
                        use_grind=config.use_grind,
                    )
                )

    _, plausible_msg = await metric_lean_compile(plausible_lean_content)
    if plausible_msg != "TIMEOUT" and "COMPERROR" not in plausible_msg:
        score = update_spec_plausible_scores(
            template_engine,
            score,
            evaluate_type,
            plausible_msg,
            config.use_plausible_pass,
        )
    else:
        print(f"Lean compile failed for plausible tests: {plausible_msg}")

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
    template_engine: LeanGenerationTaskTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
) -> str:
    lean_content = (
        template_engine.render_imports(benchmark_data.lean_data.task_imports, "task")
        + "\n"
    )
    lean_content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    lean_content += (
        template_engine.render_aux(benchmark_data.lean_data.task_aux, "task") + "\n"
    )

    lean_content += (
        template_engine.render_aux(
            make_spec_aux_testable(artifact.precond_aux), "precond"
        )
        + "\n"
    )
    lean_content += (
        template_engine.render_precond(artifact.precond, precond_name=precond_name)
        + "\n"
    )

    if evaluate_type == "postcond":
        lean_content += (
            template_engine.render_aux(
                make_spec_aux_testable(artifact.postcond_aux), "postcond"
            )
            + "\n"
        )
        lean_content += (
            template_engine.render_postcond(
                artifact.postcond,
                precond_name=precond_name,
                postcond_name=postcond_name,
            )
            + "\n"
        )

    return lean_content


async def metric_generated_spec_compile(
    existing_score: Optional[SpecMetricScore],
    template_engine: LeanGenerationTaskTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
) -> SpecMetricScore:
    if existing_score is not None:
        return existing_score

    lean_content = make_spec_test_content(
        template_engine,
        benchmark_data,
        artifact,
        evaluate_type,
        precond_name=precond_name,
        postcond_name=postcond_name,
    )

    can_compile, compile_err = await metric_lean_compile(lean_content)

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
    template_engine: LeanGenerationTaskTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    evaluate_type: Literal["precond", "postcond"],
    precond_name: str = "",
    postcond_name: str = "",
) -> SpecMetricScore:
    score = existing_score

    lean_content = make_spec_test_content(
        template_engine,
        benchmark_data,
        artifact,
        evaluate_type,
        precond_name=precond_name,
        postcond_name=postcond_name,
    )

    if score.can_compile:
        if config.unit_test:
            score = await metric_generated_spec_unit_tests(
                config,
                template_engine,
                lean_content,
                score,
                evaluate_type,
                benchmark_data.reject_inputs,
                benchmark_data.tests,
                precond_name,
                postcond_name,
            )

    return score


class ProofMetricScore(MetricScore):
    can_compile: bool
    error: Optional[str] = None


async def metric_generated_proof(
    template_engine: LeanGenerationTaskTemplate,
    benchmark_data: BenchmarkData,
    artifact: EvaluationTaskArtifact,
    precond_name: str = "",
    postcond_name: str = "",
) -> ProofMetricScore:
    cheat_codes = ["sorry", "admit", "axiom"]
    for code in cheat_codes:
        if code in artifact.proof_aux or code in artifact.proof:
            return ProofMetricScore(
                can_compile=False,
                error="cheatcodes like `sorry` or `admit` should not be used in proof",
            )

    lean_content = (
        template_engine.render_imports(benchmark_data.lean_data.task_imports, "task")
        + "\n"
    )
    lean_content += (
        template_engine.render_imports(artifact.imports, "llm_solution") + "\n"
    )
    lean_content += (
        template_engine.render_aux(benchmark_data.lean_data.task_aux, "task") + "\n"
    )

    lean_content += template_engine.render_aux(artifact.precond_aux, "precond") + "\n"
    lean_content += (
        template_engine.render_precond(artifact.precond, precond_name=precond_name)
        + "\n"
    )

    lean_content += template_engine.render_aux(artifact.code_aux, "code") + "\n"
    lean_content += (
        template_engine.render_code(artifact.code, precond_name=precond_name) + "\n"
    )

    lean_content += template_engine.render_aux(artifact.postcond_aux, "postcond") + "\n"
    lean_content += (
        template_engine.render_postcond(
            artifact.postcond, precond_name=precond_name, postcond_name=postcond_name
        )
        + "\n"
    )

    lean_content += template_engine.render_aux(artifact.proof_aux, "proof") + "\n"
    lean_content += (
        template_engine.render_proof(
            artifact.proof, precond_name=precond_name, postcond_name=postcond_name
        )
        + "\n"
    )

    can_compile, compile_err = await metric_lean_compile(lean_content)
    return ProofMetricScore(can_compile=can_compile, error=compile_err)
