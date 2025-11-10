import tomllib
from pathlib import Path
from typing import List, Literal, NewType, Optional

from pydantic import BaseModel, Field

from verina.baseline.config import BaselineConfig
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
