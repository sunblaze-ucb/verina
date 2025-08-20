from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.dsprover2.dsprover2_baseline import DSProver2BaselineSolution
from verina.baseline.dsprover2.dsprover2_proof_refinement import (
    DSProver2ProofRefinementSolution,
)
from verina.baseline.proof_refinement import ProofRefinementSolution
from verina.benchmark.solution import Solution

__all__ = [
    "BaselineConfig",
    "BaselineSolution",
    "ProofRefinementSolution",
    "DSProver2BaselineSolution",
    "DSProver2ProofRefinementSolution",
]


def get_baseline(config: BaselineConfig) -> Solution:
    """
    Get the baseline solution based on the config.
    """
    if config.name == "baseline":
        return BaselineSolution(config)
    elif config.name == "dsprover_baseline":
        return DSProver2BaselineSolution(config)
    elif config.name == "proof_refinement":
        return ProofRefinementSolution(config)
    elif config.name == "dsprover_proof_refinement":
        return DSProver2ProofRefinementSolution(config)
    else:
        raise ValueError(f"Unknown baseline solution: {config.name}")
