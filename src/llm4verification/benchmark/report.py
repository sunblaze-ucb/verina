import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

from prefect.logging import get_run_logger
from pydantic import BaseModel

from llm4verification.benchmark.common import BenchmarkRunConfig


class EvaluationTaskArtifact(BaseModel):
    imports: str = ""
    code_aux: str = ""
    code: str = ""
    precond_aux: str = ""
    precond: str = ""
    postcond_aux: str = ""
    postcond: str = ""
    proof_aux: str = ""
    proof: str = ""


class EvaluationTaskFlags(BaseModel):
    code: bool = False
    spec: bool = False
    proof: bool = False

    @staticmethod
    def gen_code() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=True, spec=False, proof=False)

    @staticmethod
    def gen_spec() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=False, spec=True, proof=False)

    @staticmethod
    def gen_proof() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=False, spec=False, proof=True)

    @staticmethod
    def gen_code_spec() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=True, spec=True, proof=False)

    @staticmethod
    def gen_code_proof() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=True, spec=False, proof=True)

    @staticmethod
    def gen_spec_proof() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=False, spec=True, proof=True)

    @staticmethod
    def gen_code_spec_proof() -> "EvaluationTaskFlags":
        return EvaluationTaskFlags(code=True, spec=True, proof=True)


class EvaluationTaskOptions(BaseModel):
    with_ref_spec: bool = False
    with_spec_desc: bool = False
    with_ref_code: bool = False


class EvaluationTaskReport(BaseModel):
    task_name: str
    data_id: str
    fewshot_example_names: List[str]
    task_flags: EvaluationTaskFlags
    task_options: EvaluationTaskOptions
    artifact: EvaluationTaskArtifact
    extra_info: Dict[str, Any] = {}
    scores: Dict[str, Any] = {}


class EvaluationDataReport(BaseModel):
    data_id: str
    task_reports: Dict[str, EvaluationTaskReport]

    @classmethod
    def parse_dict(
        cls, task_reports: Dict[str, EvaluationTaskReport]
    ) -> "EvaluationDataReport":
        """
        Create an EvaluationDataReport from a dictionary of task reports.
        Uses the data_id from any of the task reports since they all share the same data name.

        Args:
            task_reports: Dictionary mapping task names to their evaluation reports

        Returns:
            EvaluationDataReport with the task reports and data name
        """
        any_task_report = next(iter(task_reports.values()))
        data_id = any_task_report.data_id

        return cls(data_id=data_id, task_reports=task_reports)


class EvaluationExperimentReport(BaseModel):
    experiment_id: str
    data_reports: Dict[str, EvaluationDataReport]

    def sanitize_datapoints(self, valid_datapoint_names: List[str]) -> None:
        """
        Remove all data reports that are not in the valid_datapoint_names list.
        This is used to remove data reports that are not in the current round of evaluation.
        """
        self.data_reports = {
            k: v for k, v in self.data_reports.items() if k in valid_datapoint_names
        }

    def save(self, output_dir: Path, prefix: str = "") -> None:
        """Save the experiment report as JSON."""
        filename = f"{prefix}report.json"
        output_path = output_dir / filename
        with open(output_path, "w") as f:
            json_data = self.model_dump(mode="json")
            json.dump(json_data, f, indent=2, ensure_ascii=False)
            logger = get_run_logger()
            logger.info(f"Saved experiment report to {output_path}")


class EvaluationRoundsReport(BaseModel):
    config: BenchmarkRunConfig
    generation_timestamp: int = 0
    evaluated_version_timestamp: int = 0
    evaluation_timestamp: int = 0
    rounds: Dict[int, EvaluationExperimentReport]

    @staticmethod
    def get_all_versions(
        output_dir: Path,
    ) -> List[Path]:
        """Get all JSON files in the output directory."""
        # Get all JSON files in the output directory
        json_files = list(output_dir.glob("rounds_report_*.json"))

        # Sort files by timestamp in descending order
        json_files.sort(key=lambda x: x.stem.split("_")[-1], reverse=True)
        return json_files

    @staticmethod
    def load(report_path: Path) -> Optional["EvaluationRoundsReport"]:
        """Load the rounds report from the given path."""
        if not report_path.exists():
            return None
        with open(report_path, "r") as f:
            json_data = json.load(f)
            rounds_report = EvaluationRoundsReport.model_validate(json_data)
            print(f"Loaded rounds report from {report_path}")
            return rounds_report

    @staticmethod
    def load_latest(output_dir: Path) -> Optional["EvaluationRoundsReport"]:
        """Load the rounds report with newsest timestamp postfix from the output directory."""
        # Get all JSON files in the output directory
        json_files = EvaluationRoundsReport.get_all_versions(output_dir)

        # Load the latest file
        if json_files:
            latest_file = json_files[0]
            return EvaluationRoundsReport.load(latest_file)
        else:
            return None

    def sanitize_datapoints(self, valid_datapoint_names: List[str]) -> None:
        """
        Remove all data reports that are not in the valid_datapoint_names list.
        This is used to remove data reports that are not in the current round of evaluation.
        """
        for round_report in self.rounds.values():
            round_report.sanitize_datapoints(valid_datapoint_names)

    def save(self, output_dir: Path) -> None:
        """Save the rounds report as JSON."""
        timestamp = int(datetime.now().timestamp())
        filename = f"rounds_report_{timestamp}.json"
        output_path = output_dir / filename
        with open(output_path, "w") as f:
            json_data = self.model_dump(mode="json")
            json.dump(json_data, f, indent=2, ensure_ascii=False)
            try:
                logger = get_run_logger()
                logger.info(f"Saved rounds report to {output_path}")
            except Exception:
                print(f"Saved rounds report to {output_path}")
