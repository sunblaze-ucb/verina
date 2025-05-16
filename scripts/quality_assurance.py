import asyncio
import os
import random
from pathlib import Path
from typing import List, Tuple

import litellm
import typer
from dotenv import load_dotenv
from typing_extensions import Annotated

from llm4verification.benchmark import Benchmark
from llm4verification.benchmark.common import BenchmarkRunConfig, ExperimentId
from llm4verification.dataset.dataset import load_dataset
from llm4verification.dataset.schema import BenchmarkData
from llm4verification.lean import clean_playground

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
):
    # Load configuration
    config = BenchmarkRunConfig.from_toml_file(Path(config_path))
    assert config.run_type == "qa", "Run type must be 'qa' for quality assurance"

    print(f"Running quality assurance with config: {config.model_dump_json(indent=2)}")

    dataset = load_dataset()
    #     wanted = ['lab_LongestIncreasingSubsequence_324999618', 'lab_LongestCommonSubsequence_324999618',
    # 'lab_isValidParentheses_325002190', 'lab_LongestCommonSubsequence_325033255', 'lab_longestConsecutive_325601349',
    # 'lab_longestCommonSubstring_325744471', 'lab_longestCommonSubsequence_325767793',
    # 'lab_longestIncreasingSubsequence_325773003', 'lab_task_code_325773191']
    # wanted = [
    #     'lab_generateSpiralMatrix_324720188',
    # ]
    # dataset = [data for data in dataset if data.data_id in wanted]

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
