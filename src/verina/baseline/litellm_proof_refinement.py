from typing import List, Optional

from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.generate import (
    dspy_generate_proof,
    dspy_generate_proof_with_refinement,
    proof_lean_content_from_input_output,
    litellm_generate_proof,
    litellm_generate_proof_with_refinement,
)
from verina.baseline.proof_refinement import ProofRefinementSolution
from verina.benchmark.metrics import metric_lean_compile
from verina.benchmark.report import EvaluationTaskArtifact
from verina.benchmark.solution import (
    FewshotExample,
    GenProofInput,
    GenProofOutput,
)
from verina.utils.logging import logger


class LiteLLMProofRefinementSolution(ProofRefinementSolution):
    def __init__(self, config: BaselineConfig):
        super().__init__(config)

    @staticmethod
    def name() -> str:
        return "proof_refinement_baseline"

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
            output = await litellm_generate_proof(
                self.dspy_module,
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
                output = await litellm_generate_proof_with_refinement(
                    self.dspy_module, input, output, error_message
                )
            except Exception as e:
                logger.error(f"Error during proof refinement: {e}")
        return output
