from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.proof_refinement import ProofRefinementSolution
from verina.baseline.litellm_baseline import LiteLLMBaselineSolution
from verina.baseline.litellm_proof_refinement import LiteLLMProofRefinementSolution
from verina.benchmark.solution import Solution
from verina.benchmark.common import BenchmarkRunConfig


__all__ = ["BaselineConfig", "BaselineSolution", "ProofRefinementSolution"]


def get_baseline(config: BenchmarkRunConfig) -> Solution:
    """
    Get the baseline solution based on the config.
    """
    if config.baseline_config.name == "baseline":
        if (config.gen_lm_config.model_name == "deepseek-ai/DeepSeek-Prover-V2-7B" and
            config.proof_gen and not config.code_gen and not config.spec_gen and 
            not config.code_spec_gen and not config.code_proof_gen and 
            not config.spec_proof_gen and not config.code_spec_proof_gen):
            return LiteLLMBaselineSolution(config.baseline_config)
        return BaselineSolution(config.baseline_config)
    elif config.baseline_config.name == "proof_refinement":
        if (config.gen_lm_config.model_name == "deepseek-ai/DeepSeek-Prover-V2-7B" and
            config.proof_gen and not config.code_gen and not config.spec_gen and 
            not config.code_spec_gen and not config.code_proof_gen and 
            not config.spec_proof_gen and not config.code_spec_proof_gen):
            return LiteLLMProofRefinementSolution(config.baseline_config)
        return ProofRefinementSolution(config.baseline_config)
    else:
        raise ValueError(f"Unknown baseline solution: {config.baseline_config.name}")
