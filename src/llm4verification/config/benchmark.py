"""Benchmark configuration module."""

import os
from pathlib import Path
from typing import Any, Dict, Optional

import yaml
from pydantic import BaseModel, Field


class TaskConfig(BaseModel):
    """Configuration for which benchmark tasks to run."""

    code_gen: bool = Field(True, description="Whether to run code generation task")
    spec_gen: bool = Field(
        True, description="Whether to run specification generation task"
    )
    proof_gen: bool = Field(True, description="Whether to run proof generation task")
    code_spec_gen: bool = Field(
        True, description="Whether to run code and specification generation task"
    )
    code_spec_proof_gen: bool = Field(
        True,
        description="Whether to run code, specification, and proof generation task",
    )


class BenchmarkConfig(BaseModel):
    """Configuration for benchmark experiments."""

    output_dir: str = Field(..., description="Output directory for benchmark results")
    model_name: str = Field("gpt-4o-mini", description="LLM model name to use")
    provider: str = Field(
        "openai", description="LLM provider (openai, anthropic, etc.)"
    )
    rounds: int = Field(3, description="Number of rounds to run the benchmark")
    api_base: Optional[str] = Field(
        None, description="Custom API base URL for the provider"
    )
    processes: int = Field(1, description="Number of parallel processes to use")
    rm: bool = Field(True, description="Whether to remove previous benchmark results")
    task_config: TaskConfig = Field(
        default_factory=TaskConfig, description="Configuration for which tasks to run"
    )

    @classmethod
    def from_file(cls, config_path: str) -> "BenchmarkConfig":
        """Load configuration from a YAML file.

        Args:
            config_path: Path to the configuration file

        Returns:
            Loaded configuration object
        """
        path = Path(config_path)
        if not path.exists():
            raise FileNotFoundError(f"Configuration file not found: {config_path}")

        with open(path, "r") as f:
            config_data = yaml.safe_load(f)

        return cls(**config_data)

    @classmethod
    def default_path(cls) -> str:
        """Get the default configuration file path.

        Returns:
            Path to the default configuration file
        """
        # Check for config in current directory
        if Path("benchmark_config.yaml").exists():
            return "benchmark_config.yaml"

        # Check for config in user's config directory
        config_dir = os.path.expanduser("~/.config/llm4verification")
        if Path(f"{config_dir}/benchmark_config.yaml").exists():
            return f"{config_dir}/benchmark_config.yaml"

        # Default to package config
        pkg_dir = Path(__file__).parent
        return str(pkg_dir / "defaults" / "benchmark_config.yaml")

    def to_dict(self) -> Dict[str, Any]:
        """Convert configuration to dictionary.

        Returns:
            Dictionary representation of the configuration
        """
        return self.model_dump()

    def save(self, path: str) -> None:
        """Save configuration to a YAML file.

        Args:
            path: Path to save the configuration
        """
        with open(path, "w") as f:
            yaml.dump(self.to_dict(), f, default_flow_style=False)
