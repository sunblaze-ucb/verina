from typing import Literal, Tuple, Type

from dspy import (
    LM,
    InputField,
    Module,
    OutputField,
    Predict,
)
from dspy import Signature as DspySignature

from llm4verification.benchmark.solution import GenSpecOutput
from llm4verification.dataset.schema import BenchmarkData
from llm4verification.dataset.template import (
    LeanGenerationTaskTemplate,
)


def create_placeholder(name: str) -> str:
    return "{{" + f"`{name}` WILL BE FILLED HERE" + "}}"


GEN_PROOF_PROMPT = """
You are an expert in Lean 4 programming and theorem proving.
Please generate a Lean 4 proof for the example theorem provided in `theorem`.
The `theorem` is a Lean 4 code snippet that contains placeholders (warpped with {{}}) where the proof should be generated.
The proof should:
- Follow Lean 4 best practices and use appropriate Lean 4 syntax and features
- DO NOT use Lean 3 syntax or features
- DO NOT import Std or Init
Hint:
- Unfold the definitions when necessary
""".strip()


class SpecMetricProofSig(DspySignature):
    theorem = InputField()
    proof = OutputField(desc="Generated Lean 4 proof of the `theorem`.")


SpecMetricProofSig.instructions = GEN_PROOF_PROMPT


def formal_proof_theorem_from_output(
    tempalate_engine: LeanGenerationTaskTemplate,
    spec_lean_content: str,
    data: BenchmarkData,
    output: GenSpecOutput,
    target: Literal["precond", "postcond"],
    type: Literal["sound", "complete"],
    inverse: bool,
) -> str:
    theorem = (
        tempalate_engine.render_imports(data.lean_data.solution_imports, "solution")
        + "\n"
        + spec_lean_content
    )
    # render ground truth precond aux
    theorem += "\n" + tempalate_engine.render_aux(
        data.lean_data.precond_aux, "ground_truth_precond_aux"
    )
    if target == "postcond":
        theorem += "\n" + tempalate_engine.render_aux(
            data.lean_data.postcond_aux, "ground_truth_postcond_aux"
        )

    if target == "precond":
        if type == "sound":
            if inverse:
                theorem += "\n" + tempalate_engine.render_precond_formal_unsoundness(
                    generated_precond=output.precond,
                    ground_truth_precond=data.lean_data.precond,
                    proof=create_placeholder("proof"),
                )
            else:
                theorem += "\n" + tempalate_engine.render_precond_formal_soundness(
                    generated_precond=output.precond,
                    ground_truth_precond=data.lean_data.precond,
                    proof=create_placeholder("proof"),
                )
        else:
            if inverse:
                theorem += "\n" + tempalate_engine.render_precond_formal_soundness(
                    generated_precond=output.precond,
                    ground_truth_precond=data.lean_data.precond,
                    proof=create_placeholder("proof"),
                )
            else:
                theorem += "\n" + tempalate_engine.render_precond_formal_unsoundness(
                    generated_precond=output.precond,
                    ground_truth_precond=data.lean_data.precond,
                    proof=create_placeholder("proof"),
                )
    elif target == "postcond":
        if type == "sound":
            if inverse:
                theorem += "\n" + tempalate_engine.render_postcond_formal_unsoundness(
                    ground_truth_precond=data.lean_data.precond,
                    generated_postcond=output.postcond,
                    ground_truth_postcond=data.lean_data.postcond,
                    proof=create_placeholder("proof"),
                )
            else:
                theorem += "\n" + tempalate_engine.render_postcond_formal_soundness(
                    ground_truth_precond=data.lean_data.precond,
                    generated_postcond=output.postcond,
                    ground_truth_postcond=data.lean_data.postcond,
                    proof=create_placeholder("proof"),
                )
        else:
            if inverse:
                theorem += "\n" + tempalate_engine.render_postcond_formal_soundness(
                    ground_truth_precond=data.lean_data.precond,
                    generated_postcond=output.postcond,
                    ground_truth_postcond=data.lean_data.postcond,
                    proof=create_placeholder("proof"),
                )
            else:
                theorem += "\n" + tempalate_engine.render_postcond_formal_unsoundness(
                    ground_truth_precond=data.lean_data.precond,
                    generated_postcond=output.postcond,
                    ground_truth_postcond=data.lean_data.postcond,
                    proof=create_placeholder("proof"),
                )
    return theorem


def unit_test_theorem_from_output(
    tempalate_engine: LeanGenerationTaskTemplate,
    spec_lean_content: str,
    data: BenchmarkData,
    test_idx: int | Tuple[int, int],
    output: GenSpecOutput,
    target: Literal["precond", "postcond"],
    type: Literal["sound", "complete"],
    inverse: bool,
) -> str:
    theorem = spec_lean_content
    if target == "precond":
        assert isinstance(test_idx, int)
        if type == "sound":
            theorem += (
                "\n"
                + tempalate_engine.render_precond_unit_test_sound_undecidable(
                    data.tests[test_idx],
                    test_idx=test_idx,
                    test_type="llm",
                    test_proof=create_placeholder("proof"),
                    inverse=inverse,
                )
            )
        else:
            theorem += (
                "\n"
                + tempalate_engine.render_precond_unit_test_complete_undecidable(
                    data.reject_inputs[test_idx],
                    test_idx=test_idx,
                    test_type="llm",
                    test_proof=create_placeholder("proof"),
                    inverse=inverse,
                )
            )
    elif target == "postcond":
        if type == "sound":
            assert isinstance(test_idx, tuple) and len(test_idx) == 2
            theorem += (
                "\n"
                + tempalate_engine.render_postcond_unit_test_sound_undecidable(
                    data.tests[test_idx[0]],
                    test_idx=test_idx[0],
                    unexpected_idx=test_idx[1],
                    test_type="llm",
                    test_proof=create_placeholder("proof"),
                    inverse=inverse,
                )
            )
        else:
            assert isinstance(test_idx, int)
            theorem += (
                "\n"
                + tempalate_engine.render_postcond_unit_test_complete_undecidable(
                    data.tests[test_idx],
                    test_idx=test_idx,
                    test_type="llm",
                    test_proof=create_placeholder("proof"),
                    inverse=inverse,
                )
            )
    return theorem


class SpecLLMMetric:
    def __init__(
        self,
        lm: LM,
        module: Type[Module] = Predict,
    ):
        self.lm = lm
        self.module = module

    def gen_formal_proof(
        self,
        tempalate_engine: LeanGenerationTaskTemplate,
        spec_lean_content: str,
        data: BenchmarkData,
        output: GenSpecOutput,
        target: Literal["precond", "postcond"],
        type: Literal["sound", "complete"],
        inverse: bool,
    ) -> str:
        theorem = formal_proof_theorem_from_output(
            tempalate_engine, spec_lean_content, data, output, target, type, inverse
        )
        generator = self.module(SpecMetricProofSig)
        response = generator(
            theorem=theorem,
            lm=self.lm,
        )
        return response.proof

    def gen_unit_test_proof(
        self,
        tempalate_engine: LeanGenerationTaskTemplate,
        spec_lean_content: str,
        data: BenchmarkData,
        test_idx: int | Tuple[int, int],
        output: GenSpecOutput,
        target: Literal["precond", "postcond"],
        type: Literal["sound", "complete"],
        inverse: bool,
    ) -> str:
        theorem = unit_test_theorem_from_output(
            tempalate_engine,
            spec_lean_content,
            data,
            test_idx,
            output,
            target,
            type,
            inverse,
        )
        generator = self.module(SpecMetricProofSig)
        response = generator(
            theorem=theorem,
            lm=self.lm,
        )
        return response.proof
