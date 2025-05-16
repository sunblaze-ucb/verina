from llm4verification.baseline.baseline import BaselineSolution
from llm4verification.baseline.config import BaselineConfig
from llm4verification.baseline.proof_refinement import ProofRefinementSolution
from llm4verification.benchmark.solution import Solution

__all__ = ["BaselineConfig", "BaselineSolution", "ProofRefinementSolution"]


def get_baseline(config: BaselineConfig) -> Solution:
    """
    Get the baseline solution based on the config.
    """
    if config.name == "baseline":
        return BaselineSolution(config)
    elif config.name == "proof_refinement":
        return ProofRefinementSolution(config)
    else:
        raise ValueError(f"Unknown baseline solution: {config.name}")
