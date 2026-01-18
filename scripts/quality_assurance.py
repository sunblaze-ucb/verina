import asyncio
import os
import random
from pathlib import Path
from typing import List, Tuple

import litellm
import typer
from dotenv import load_dotenv
from typing_extensions import Annotated

from verina.benchmark import Benchmark
from verina.benchmark.common import BenchmarkRunConfig, ExperimentId
from verina.coq import clean_coq_playground
from verina.dataset.dataset import load_dataset
from verina.dataset.schema import BenchmarkData
from verina.lean import clean_playground

load_dotenv()

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
    data_filter: Annotated[str, typer.Option("--data", "-d", help="Filter to specific data ID(s), comma-separated")] = "",
):
    # Load configuration
    config = BenchmarkRunConfig.from_toml_file(Path(config_path))
    assert config.run_type == "qa", "Run type must be 'qa' for quality assurance"

    print(f"Running quality assurance with config: {config.model_dump_json(indent=2)}")

    dataset = load_dataset()

    # Filter dataset by data ID if specified
    if data_filter:
        wanted = [d.strip() for d in data_filter.split(",")]
        dataset = [data for data in dataset if data.data_id in wanted]
        print(f"Filtered to {len(dataset)} data points: {[d.data_id for d in dataset]}")

    if config.itp_type == "coq":
        clean_coq_playground()
    else:
        clean_playground()
    Path(config.output_dir).mkdir(parents=True, exist_ok=True)

    benchmark = Benchmark(config)

    asyncio.run(
        benchmark.run_quality_assurance(
            ExperimentId(config.output_dir),
            dataset,
        )  # type: ignore
    )


if __name__ == "__main__":
    typer.run(main)
