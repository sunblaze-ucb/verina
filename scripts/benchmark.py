import asyncio
import os
import random
from pathlib import Path
from typing import List, Optional, Tuple

import dspy
import litellm
import typer
from dotenv import load_dotenv
from typing_extensions import Annotated

from verina.baseline.common import get_baseline
from verina.benchmark import Benchmark
from verina.benchmark.common import BenchmarkRunConfig, ExperimentId
from verina.benchmark.report import EvaluationRoundsReport
from verina.dataset.dataset import load_dataset
from verina.dataset.schema import BenchmarkData

load_dotenv(override=True)

litellm.vertex_project = os.getenv("VERTEX_PROJECT_ID")
litellm.vertex_location = os.getenv("VERTEX_LOCATION")
litellm.success_callback = ["langfuse"]
litellm.failure_callback = ["langfuse"]


random.seed(42)


def get_split_by_data_id(
    dataset: List[BenchmarkData], ids: List[str]
) -> Tuple[List[BenchmarkData], List[BenchmarkData]]:
    """Split the dataset into two parts based on the data IDs.

    Args:
        dataset: List of BenchmarkData objects.
        ids: List of data IDs to split by.

    Returns:
        Tuple of two lists: the first list contains the data with the specified data IDs,
        and the second list contains the rest of the data.
    """
    filtered_data = [data for data in dataset if data.data_id in ids]
    remaining_data = [data for data in dataset if data.data_id not in ids]
    return filtered_data, remaining_data


def main(
    config_path: Annotated[str, typer.Option("--config", "-c")],
    no_gen: Annotated[bool, typer.Option("--no-gen")] = False,
    no_eval: Annotated[bool, typer.Option("--no-eval")] = False,
    eval_workers: Annotated[
        Optional[int], typer.Option("--eval-workers", "-ew")
    ] = None,
    filter_pattern: Annotated[
        Optional[str], typer.Option("--filter", "-f", help="Filter data points by pattern in data_id (e.g., 'basic', 'advanced')")
    ] = None,
    limit: Annotated[
        Optional[int], typer.Option("--limit", "-l", help="Limit the number of data points to run")
    ] = None,
):
    # Load configuration
    config = BenchmarkRunConfig.from_toml_file(Path(config_path))
    if config.run_type == "qa":
        raise ValueError(
            "The run type 'qa' is not supported for this script. Please use 'quality_assurance.py' instead."
        )

    # override run type
    if no_gen:
        config.run_type = "evaluate_only"
        if eval_workers is not None:
            config.max_workers = eval_workers
    elif no_eval:
        config.run_type = "generate_only"

    print(f"Running benchmark with config: {config.model_dump_json(indent=2)}")

    lm = config.gen_lm_config.get_model()
    dspy.configure(lm=lm)

    dataset = load_dataset()

    # Apply filter if specified
    if filter_pattern:
        dataset = [data for data in dataset if filter_pattern in data.data_id]
        print(f"Filtered to {len(dataset)} data points matching '{filter_pattern}'")

    # Apply limit if specified
    if limit:
        dataset = dataset[:limit]
        print(f"Limited to {len(dataset)} data points")

    # clean_playground()
    Path(config.output_dir).mkdir(parents=True, exist_ok=True)

    fewshot_examples, dataset = get_split_by_data_id(
        dataset, config.fewshot_example_names
    )

    # Propagate itp_type from top-level config to baseline_config
    config.baseline_config.itp_type = config.itp_type
    baseline = get_baseline(config.baseline_config)
    benchmark = Benchmark(config)

    latest_report = EvaluationRoundsReport.load_latest(Path(config.output_dir))

    # asyncio.run(benchmark.evaluate(ExperimentId(config.output_dir), baseline, dataset, []))  # type: ignore
    asyncio.run(
        benchmark.benchmark_multi_round(
            ExperimentId(config.output_dir),
            config.rounds,
            baseline,
            dataset,
            fewshot_examples,
            latest_report,
        )  # type: ignore
    )


if __name__ == "__main__":
    typer.run(main)
