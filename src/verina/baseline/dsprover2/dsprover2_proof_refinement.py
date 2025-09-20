from typing import List, Optional

import dspy

from verina.baseline.config import BaselineConfig
from verina.baseline.generate import proof_lean_content_from_input_output
from verina.baseline.dsprover2.dsprover2_generate import (
    dsprover2_generate_proof,
    dsprover2_generate_proof_with_refinement,
)
from verina.benchmark.metrics import metric_lean_compile
from verina.benchmark.report import EvaluationTaskArtifact
from verina.benchmark.solution import (
    FewshotExample,
    GenCodeInput,
    GenCodeOutput,
    GenProofInput,
    GenProofOutput,
    GenSpecInput,
    GenSpecOutput,
    SimpleSolution,
)
from verina.utils.logging import logger


class DSProver2ProofRefinementSolution(SimpleSolution):
    def __init__(self, config: BaselineConfig):
        self.config = config

        if config.combind_task_preference == "NO_GENERATED_AS_REF":
            preference = SimpleSolution.Preference.NO_GENERATED_AS_REF
        elif config.combind_task_preference == "USE_GENERATED_CODE_AS_REF":
            preference = SimpleSolution.Preference.USE_GENERATED_CODE_AS_REF
        elif config.combind_task_preference == "USE_GENERATED_SPEC_AS_REF":
            preference = SimpleSolution.Preference.USE_GENERATED_SPEC_AS_REF
        else:
            raise ValueError(
                f"Unknown combind task preference: {config.combind_task_preference}. "
                "Please use 'NO_GENERATED_AS_REF', 'USE_GENERATED_CODE_AS_REF', or 'USE_GENERATED_SPEC_AS_REF'."
            )

        super().__init__(preference)

    def get_lm(self) -> dspy.LM:
        return dspy.settings.lm

    @staticmethod
    def name() -> str:
        return "dsprover_proof_refinement_baseline"

    async def gen_code(
        self,
        data_id: str,
        input: GenCodeInput,
        fewshot_examples: List[FewshotExample[GenCodeInput, GenCodeOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeOutput:
        raise NotImplementedError

    async def gen_spec(
        self,
        data_id: str,
        input: GenSpecInput,
        fewshot_examples: List[FewshotExample[GenSpecInput, GenSpecOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenSpecOutput:
        raise NotImplementedError

    async def gen_proof(
        self,
        data_id: str,
        input: GenProofInput,
        fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenProofOutput:
        # We don't use checkpoint for proof refinement
        # TODO: figure out checkpoint
        try:
            output = await dsprover2_generate_proof(
                self.get_lm(),
                input,
                fewshot_examples,
            )
        except Exception as e:
            logger.error(f"Error during proof generation: {e}")
            output = GenProofOutput(
                imports="",
                proof_aux="",
                proof="",
            )

        if self.config.refinements is None:
            return output

        refined_times = 0
        while refined_times < self.config.refinements:
            refined_times += 1
            logger.info(
                f"Refining proof for data_id {data_id} for the {refined_times} time"
            )

            # Check if the proof is correct
            if output.proof != "":
                cheat_codes = ["sorry", "admit", "axiom"]
                if any(code in output.proof for code in cheat_codes) or any(
                    code in output.proof_aux for code in cheat_codes
                ):
                    can_compile = False
                    error_message = "Proof contains cheat codes."
                else:
                    lean_content = proof_lean_content_from_input_output(input, output)
                    can_compile, error_message = await metric_lean_compile(lean_content)
            else:
                can_compile = False
                error_message = "Failed to generate proof. The model response does not follow the expected format."
            if can_compile:
                output.extra_info["refined_times"] = refined_times
                return output
            try:
                output = await dsprover2_generate_proof_with_refinement(
                    self.get_lm(), input, output, error_message
                )
            except Exception as e:
                logger.error(f"Error during proof refinement: {e}")
        return output
