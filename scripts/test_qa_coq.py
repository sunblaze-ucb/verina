"""Test QA for Coq with QuickChick on a specific datapoint."""
import asyncio
from pathlib import Path

from verina.benchmark import Benchmark
from verina.benchmark.common import BenchmarkRunConfig, ExperimentId
from verina.dataset.dataset import load_dataset
from verina.coq import clean_coq_playground

def main():
    # Load configuration
    config = BenchmarkRunConfig.from_toml_file(Path("configs/qa_coq.toml"))
    assert config.run_type == "qa", "Run type must be 'qa' for quality assurance"

    print(f"ITP type: {config.itp_type}")
    print(f"Coq config: {config.coq_config}")

    # Load dataset and filter to specific datapoint
    dataset = load_dataset()
    target_id = "verina_advanced_1"
    dataset = [data for data in dataset if data.data_id == target_id]

    if not dataset:
        print(f"Error: datapoint {target_id} not found")
        return

    print(f"Running QA on: {dataset[0].data_id}")
    print(f"Coq data available: {dataset[0].coq_data is not None}")

    if dataset[0].coq_data:
        print(f"Coq code: {dataset[0].coq_data.code[:100]}...")
        print(f"Coq precond: {dataset[0].coq_data.precond[:100]}...")

    # Clean playground
    clean_coq_playground()
    Path(config.output_dir).mkdir(parents=True, exist_ok=True)

    # Run QA
    benchmark = Benchmark(config)
    asyncio.run(
        benchmark.run_quality_assurance(
            ExperimentId(config.output_dir),
            dataset,
        )
    )

    print(f"\nQA complete! Results saved to: {config.output_dir}")

if __name__ == "__main__":
    main()
