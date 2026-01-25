import json
from pathlib import Path
from typing import List, Optional

from verina.dataset.parsing import parse_benchmark_lean_data
from verina.dataset.schema import (
    BenchmarkData,
    RejectInput,
    Signature,
    SpecDesc,
    TestCase,
)
from verina.utils.logging import logger
from verina.utils.path import ROOT_DIR

LEAN_VERINA_PATH = ROOT_DIR / "datasets" / "verina"


def parse_reject_inputs_file(reject_inputs_path: Path) -> List[RejectInput]:
    """Parse a test.json file to extract test cases.

    Args:
        test_path: Path to the test.json file

    Returns:
        List of TestCase objects
    """
    try:
        with open(reject_inputs_path, "r") as f:
            test_data = json.load(f)

        # Ensure test_data is a list of test cases
        if not isinstance(test_data, list):
            logger.warning(f"Invalid reject_inputs.json format in {reject_inputs_path}")
            return []

        # Convert raw test data into TestCase objects
        reject_inputs = []
        for reject_input in test_data:
            try:
                reject_inputs.append(
                    RejectInput(
                        input=reject_input.get("input", {}),
                    )
                )
            except Exception as e:
                logger.warning(
                    f"Error parsing reject input in {reject_inputs_path}: {str(e)}"
                )
                continue

        return reject_inputs

    except Exception as e:
        logger.warning(
            f"Error reading reject_inputs.json at {reject_inputs_path}: {str(e)}"
        )
        return []


def parse_test_file(test_path: Path) -> List[TestCase]:
    """Parse a test.json file to extract test cases.

    Args:
        test_path: Path to the test.json file

    Returns:
        List of TestCase objects
    """
    try:
        with open(test_path, "r") as f:
            test_data = json.load(f)

        # Ensure test_data is a list of test cases
        if not isinstance(test_data, list):
            logger.warning(f"Invalid test.json format in {test_path}")
            return []

        # Convert raw test data into TestCase objects
        test_cases = []
        for test_case in test_data:
            try:
                test_cases.append(
                    TestCase(
                        input=test_case.get("input", {}),
                        expected=test_case.get("expected"),
                        unexpected=test_case.get("unexpected", []),
                    )
                )
            except Exception as e:
                logger.warning(f"Error parsing test case in {test_path}: {str(e)}")
                continue

        return test_cases

    except Exception as e:
        logger.warning(f"Error reading test.json at {test_path}: {str(e)}")
        return []


def load_benchmark_data_from_task_file(
    task_dir: Path, task_path: Path
) -> BenchmarkData:
    if not task_path.exists():
        raise FileNotFoundError(f"Task file {task_path} does not exist")
    task_data = json.loads(task_path.read_text())
    task_id = task_data.get("id", None)
    if not task_id:
        raise ValueError(f"Task ID not found in {task_path}")

    # Read description.txt
    desc_path = task_dir / task_data["description_file"]
    if not desc_path.exists():
        raise FileNotFoundError(f"Description file {desc_path} does not exist")
    description = desc_path.read_text().strip()

    # Load signature
    try:
        signature = Signature(**task_data["signature"])
    except Exception as e:
        raise ValueError(f"Error parsing signature for {task_id}: {str(e)}")

    # Read .lean file
    lean_path = task_dir / task_data["lean_file"]
    if not lean_path.exists():
        raise FileNotFoundError(f"Lean file {lean_path} does not exist")

    # implementation, specifications = parse_lean_file(lean_path)
    lean_data = parse_benchmark_lean_data(lean_path.read_text())

    spec_desc = SpecDesc(
        precond_desc=task_data["specification"]["preconditions"],
        postcond_desc=task_data["specification"]["postconditions"],
    )

    if not lean_data.code:
        raise ValueError(f"Code section is empty in {lean_path}")

    # Read reject_inputs.json
    reject_inputs_path = task_dir / task_data["reject_inputs_file"]
    reject_inputs = []
    if reject_inputs_path.exists():
        reject_inputs = parse_reject_inputs_file(reject_inputs_path)

    # Read test.json
    test_path = task_dir / task_data["test_file"]
    tests = []
    if test_path.exists():
        tests = parse_test_file(test_path)

    # Read coq_test.json if it exists (Coq-specific tests with Coq literal values)
    coq_test_path = task_dir / "coq_test.json"
    coq_tests = None
    if coq_test_path.exists():
        coq_tests = parse_test_file(coq_test_path)

    # Read coq_reject_inputs.json if it exists (Coq-specific reject inputs with Coq literal syntax)
    coq_reject_inputs_path = task_dir / "coq_reject_inputs.json"
    coq_reject_inputs = None
    if coq_reject_inputs_path.exists():
        coq_reject_inputs = parse_reject_inputs_file(coq_reject_inputs_path)

    metadata = task_data.get("metadata", {})
    metadata_json = json.dumps(metadata)

    # Load Coq signature if present
    coq_signature: Optional[Signature] = None
    if "coq_signature" in task_data:
        try:
            coq_signature = Signature(**task_data["coq_signature"])
        except Exception as e:
            logger.warning(f"Error parsing coq_signature for {task_id}: {str(e)}")

    # Read .v file if present
    coq_file = task_data.get("coq_file", None)
    coq_data = None
    if coq_file:
        coq_path = task_dir / coq_file
        if coq_path.exists():
            try:
                from verina.coq.parsing import parse_benchmark_coq_data
                coq_data = parse_benchmark_coq_data(coq_path.read_text())
            except Exception as e:
                logger.warning(f"Error parsing Coq file for {task_id}: {str(e)}")

    # Create benchmark data and convert to dict with consistent types
    benchmark_data = BenchmarkData(
        data_id=task_id,
        description=description,
        signature=signature,
        lean_data=lean_data,
        coq_signature=coq_signature,
        coq_file=coq_file,
        coq_data=coq_data,
        spec_desc=spec_desc,
        reject_inputs=reject_inputs,
        tests=tests,
        coq_tests=coq_tests,
        coq_reject_inputs=coq_reject_inputs,
        metadata=metadata_json,
    )

    return benchmark_data


def load_dataset() -> List[BenchmarkData]:
    """Read all files from task directories in the manual dataset path."""
    results: List[BenchmarkData] = []

    # Get all task directories sorted by task ID
    task_dirs = sorted(
        [d for d in LEAN_VERINA_PATH.glob("verina_*") if d.is_dir()],
        key=lambda x: int(x.name.split("_")[-1]),
    )

    for task_dir in task_dirs:
        task_id = task_dir.name

        try:
            # Read task.json
            task_path = task_dir / "task.json"
            benchmark_data = load_benchmark_data_from_task_file(task_dir, task_path)
            results.append(benchmark_data)

        except Exception as e:
            logger.error(f"Error processing {task_id}: {str(e)}")
            continue

    if len(results) == 0:
        raise ValueError("No valid tasks found in the manual dataset directory")

    return results


if __name__ == "__main__":
    try:
        # Load the dataset
        dataset = load_dataset()

        # Print summary information
        logger.info("\nDataset Summary:")
        logger.info(f"Total number of tasks: {len(dataset)}")
        logger.info(f"Tasks processed: {', '.join(item.data_id for item in dataset)}")

        # Print first element as example
        logger.info("\nExample (first element):")
        logger.info(dataset[0].model_dump_json(indent=2))

        # create jsonl file
        output_path = LEAN_VERINA_PATH / "verina_dataset.jsonl"
        with open(output_path, "w") as f:
            for item in dataset:
                f.write(item.model_dump_json() + "\n")
        logger.info(f"Dataset saved to {output_path}")

    except Exception as e:
        logger.error(f"Error: {str(e)}")
        raise
