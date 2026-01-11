import asyncio
from typing import List, Optional

from dspy import ChainOfThought, Predict

from verina.baseline.config import BaselineConfig
from verina.baseline.generate import (
    dspy_generate_code,
    dspy_generate_proof,
    dspy_generate_spec,
)
from verina.baseline.generate_coq import (
    dspy_generate_coq_code,
    dspy_generate_coq_proof,
    dspy_generate_coq_spec,
)
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


class BaselineSolution(SimpleSolution):
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

        if config.dspy_module is None or config.dspy_module == "Predict":
            self.dspy_module = Predict
        elif config.dspy_module == "ChainOfThought":
            self.dspy_module = ChainOfThought
        else:
            raise ValueError(
                f"Unknown dspy module: {config.dspy_module}. "
                "Please use 'Predict' or 'ChainOfThought'."
            )

    @staticmethod
    def name() -> str:
        return "baseline"

    async def gen_code(
        self,
        data_id: str,
        input: GenCodeInput,
        fewshot_examples: List[FewshotExample[GenCodeInput, GenCodeOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeOutput:
        if self.config.resume_from_checkpoint and checkpoint is not None:
            if checkpoint.code != "":
                logger.info(f"Use code result from checkpoint for data_id {data_id}")
                return GenCodeOutput(
                    imports=checkpoint.imports,
                    code_aux=checkpoint.code_aux,
                    code=checkpoint.code,
                )
        logger.info(f"Baseline: Generating code for data_id {data_id} (itp_type={self.config.itp_type})")
        retry_count = 0
        while retry_count < max_retries:
            try:
                if self.config.itp_type == "coq":
                    output = await dspy_generate_coq_code(
                        self.dspy_module,
                        input,
                        fewshot_examples,
                    )
                else:
                    output = await dspy_generate_code(
                        self.dspy_module,
                        input,
                        fewshot_examples,
                    )
                return output
            except Exception as e:
                logger.error(f"Error generating code for data_id {data_id}: {e}")
                retry_count += 1
                await asyncio.sleep(1)  # Optional: wait before retrying

        return GenCodeOutput(
            imports="",
            code_aux="",
            code="",
        )

    async def gen_spec(
        self,
        data_id: str,
        input: GenSpecInput,
        fewshot_examples: List[FewshotExample[GenSpecInput, GenSpecOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenSpecOutput:
        if self.config.resume_from_checkpoint and checkpoint is not None:
            if checkpoint.precond != "" or checkpoint.postcond != "":
                logger.info(f"Use spec result from checkpoint for data_id {data_id}")
                return GenSpecOutput(
                    imports=checkpoint.imports,
                    precond_aux=checkpoint.precond_aux,
                    precond=checkpoint.precond,
                    postcond_aux=checkpoint.postcond_aux,
                    postcond=checkpoint.postcond,
                )
        logger.info(f"Baseline: Generating spec for data_id {data_id} (itp_type={self.config.itp_type})")
        retry_count = 0
        while retry_count < max_retries:
            try:
                if self.config.itp_type == "coq":
                    output = await dspy_generate_coq_spec(
                        self.dspy_module,
                        input,
                        fewshot_examples,
                    )
                else:
                    output = await dspy_generate_spec(
                        self.dspy_module,
                        input,
                        fewshot_examples,
                    )
                return output
            except Exception as e:
                logger.error(f"Error generating spec for data_id {data_id}: {e}")
                retry_count += 1
                await asyncio.sleep(1)
        return GenSpecOutput(
            imports="",
            precond_aux="",
            precond="",
            postcond_aux="",
            postcond="",
        )

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
        logger.info(f"Baseline: Generating proof for data_id {data_id} (itp_type={self.config.itp_type})")
        retry_count = 0
        while retry_count < max_retries:
            try:
                if self.config.itp_type == "coq":
                    output = await dspy_generate_coq_proof(
                        self.dspy_module,
                        input,
                        fewshot_examples,
                    )
                else:
                    output = await dspy_generate_proof(
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
