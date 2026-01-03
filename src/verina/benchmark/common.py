import tomllib
from pathlib import Path
from typing import List, Literal, NewType, Optional

from pydantic import BaseModel, Field

from verina.baseline.config import BaselineConfig
from verina.itp import ITPType
from verina.utils.lm import LMConfig

ExperimentId = NewType("ExperimentId", str)
TaskId = NewType("TaskId", str)
InputId = NewType("InputId", str)
ExecutionId = NewType("ExecutionId", str)


class BenchmarkSpecEvaluationConfig(BaseModel):
    spec_proving_lm_config: Optional[LMConfig] = (
        None  # None means use the same LM as the generation
    )

    formal_proving: bool = False
    unit_test: bool = True
    unit_test_proving: bool = False

    use_grind: bool = False
    use_plausible_pass: bool = True

    # evidence
    evidence_rel_dir: str = "./evidence"
    generate_evidence_template: bool = False
    use_evidence: bool = False
    save_evidence: bool = False


class CoqEvaluationConfig(BaseModel):
    """Coq-specific evaluation configuration."""
    use_quickchick: bool = Field(
        False,
        description="Whether to use QuickChick for property-based testing",
    )
    quickchick_num_tests: int = Field(
        1000,
        description="Number of QuickChick tests to run",
    )
    docker_image: Optional[str] = Field(
        None,
        description="Docker image to use for Coq compilation (e.g., 'verina-coq'). "
                    "If None, uses local coqc. Required for QuickChick.",
    )


class BenchmarkRunConfig(BaseModel):
    # common config
    output_dir: str
    max_workers: int = 16
    run_type: Literal["benchmark", "generate_only", "evaluate_only", "qa"] = Field(
        "benchmark",
        description="Type of run: benchmark, generate_only, or evaluate_only",
    )
    rounds: int = Field(1, description="Number of rounds to run the benchmark")
    fewshot_example_names: List[str] = Field(
        default_factory=list,
        description="List of fewshot example names to use for the benchmark",
    )

    # ITP (Interactive Theorem Prover) selection
    itp_type: str = Field(
        "lean",
        description="The theorem prover to use: 'lean' or 'coq'",
    )

    # Coq-specific config (only used when itp_type='coq')
    coq_config: Optional[CoqEvaluationConfig] = Field(
        None,
        description="Coq-specific evaluation configuration",
    )

    def get_itp_type(self) -> ITPType:
        """Get the ITP type as an enum."""
        return ITPType(self.itp_type)

    # generation
    gen_lm_config: LMConfig

    baseline_config: BaselineConfig

    code_gen: bool = Field(True, description="Whether to run code generation task")
    spec_gen: bool = Field(
        True, description="Whether to run specification generation task"
    )
    proof_gen: bool = Field(True, description="Whether to run proof generation task")
    code_spec_gen: bool = Field(
        True, description="Whether to run code and specification generation task"
    )
    code_proof_gen: bool = Field(
        True, description="Whether to run code and proof generation task"
    )
    spec_proof_gen: bool = Field(
        True, description="Whether to run specification and proof generation task"
    )
    code_spec_proof_gen: bool = Field(
        True,
        description="Whether to run code, specification, and proof generation task",
    )

    # evaluation
    eval_spec_config: BenchmarkSpecEvaluationConfig = Field(
        default_factory=BenchmarkSpecEvaluationConfig,
        description="Configuration for specification evaluation",
    )

    @staticmethod
    def from_toml_file(config_path: Path) -> "BenchmarkRunConfig":
        """Load configuration from a TOML file.

        Args:
            config_path: Path to the configuration file

        Returns:
            Loaded configuration object
        """
        with open(config_path, "rb") as f:
            config_dict = tomllib.load(f)
        return BenchmarkRunConfig.model_validate(config_dict)


class TaskInput(BaseModel):
    input_id: InputId
