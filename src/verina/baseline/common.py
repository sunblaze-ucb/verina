from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.custom_prompt_proof import (
    CustomPromptProofBaselineSolution,
    CustomPromptProofRefinementBaselineSolution,
)
from verina.baseline.proof_refinement import ProofRefinementSolution
from verina.benchmark.solution import Solution

__all__ = [
    "BaselineConfig",
    "BaselineSolution",
    "ProofRefinementSolution",
    "CustomPromptProofBaselineSolution",
    "CustomPromptProofRefinementBaselineSolution",
]


def get_baseline(config: BaselineConfig) -> Solution:
    """
    Get the baseline solution based on the config.
    """
    if config.name == "baseline":
        return BaselineSolution(config)
    elif config.name == "proof_refinement":
        return ProofRefinementSolution(config)
    elif config.name == "custom_prompt_baseline":
        return CustomPromptProofBaselineSolution(config)
    elif config.name == "custom_prompt_proof_refinement_baseline":
        return CustomPromptProofRefinementBaselineSolution(config)
    else:
        raise ValueError(f"Unknown baseline solution: {config.name}")
