import asyncio
from typing import List, Optional

from dspy import ChainOfThought, Predict

from verina.baseline.config import BaselineConfig
from verina.baseline.generate import (
    dspy_generate_code,
    dspy_generate_proof,
    dspy_generate_spec,
    litellm_generate_proof
)
from verina.baseline.baseline import BaselineSolution
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

max_retries = 1  # Number of retries for errors of failures to follow dspy format


class LiteLLMBaselineSolution(BaselineSolution):
    def __init__(self, config: BaselineConfig):
        super().__init__(config)

    @staticmethod
    def name() -> str:
        return "baseline"

    async def gen_proof(
        self,
        data_id: str,
        input: GenProofInput,
        fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenProofOutput:
        if self.config.resume_from_checkpoint and checkpoint is not None:
            if checkpoint.proof != "":
                logger.info(f"Use proof result from checkpoint for data_id {data_id}")
                return GenProofOutput(
                    imports=checkpoint.imports,
                    proof_aux=checkpoint.proof_aux,
                    proof=checkpoint.proof,
                )
        logger.info(f"Baseline: Generating proof for data_id {data_id}")
        retry_count = 0
        while retry_count < max_retries:
            try:
                output = await litellm_generate_proof(
                    self.dspy_module,
                    input,
                    fewshot_examples,
                )
                return output
            except Exception as e:
                logger.error(f"Error generating proof for data_id {data_id}: {e}")
                retry_count += 1
                await asyncio.sleep(1)
        return GenProofOutput(
            imports="",
            proof_aux="",
            proof="",
        )
