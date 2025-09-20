import asyncio
from typing import List, Optional

import dspy

from verina.baseline.config import BaselineConfig
from verina.baseline.dsprover2.dsprover2_generate import dsprover2_generate_proof
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


class DSProver2BaselineSolution(SimpleSolution):
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
        return "dsprover_baseline"

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
                output = await dsprover2_generate_proof(
                    self.get_lm(),
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
