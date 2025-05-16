from typing import Any, Dict, List, Optional

from pydantic import BaseModel

from llm4verification.benchmark.metrics import (
    CodeMetricScore,
    LeanTestScore,
    ProofMetricScore,
    SpecMetricScore,
)
from llm4verification.benchmark.report import (
    EvaluationExperimentReport,
    EvaluationRoundsReport,
)
from llm4verification.utils.metrics import pass_at_k


class DatapointSummaryReport(BaseModel):
    # task name -> data_id -> metric_name -> [scores for each round]
    results: Dict[str, Dict[str, Dict[str, List[LeanTestScore]]]] = {}
    overestimate_results: Dict[str, Dict[str, Dict[str, List[LeanTestScore]]]] = {}

    @staticmethod
    def extract_score(
        scores: Dict[str, Any],
        overestimate: bool = False,
    ) -> Dict[str, LeanTestScore]:
        extracted = {}
        if "code" in scores:
            extracted["code"] = CodeMetricScore(**scores["code"]).score
        for spec in ["precond", "postcond"]:
            if spec in scores:
                spec_score = SpecMetricScore(**scores[spec])
                if not spec_score.can_compile:
                    extracted[f"{spec}_sound"] = LeanTestScore.FAIL
                    extracted[f"{spec}_complete"] = LeanTestScore.FAIL
                else:
                    extracted[f"{spec}_sound"] = spec_score.sound_test_score.score
                    extracted[f"{spec}_complete"] = spec_score.complete_test_score.score
                    if overestimate:
                        if (
                            spec_score.sound_test_score.pass_count > 0
                            and spec_score.sound_test_score.fail_count == 0
                        ):
                            extracted[f"{spec}_sound"] = LeanTestScore.PASS
                        if (
                            spec_score.complete_test_score.pass_count > 0
                            and spec_score.complete_test_score.fail_count == 0
                        ):
                            extracted[f"{spec}_complete"] = LeanTestScore.PASS
                extracted[f"{spec}_sound_complete"] = LeanTestScore.FAIL
                if (
                    extracted[f"{spec}_sound"] == LeanTestScore.PASS
                    and extracted[f"{spec}_complete"] == LeanTestScore.PASS
                ):
                    extracted[f"{spec}_sound_complete"] = LeanTestScore.PASS
        if (
            "precond_sound_complete" in extracted
            and "postcond_sound_complete" in extracted
        ):
            if (
                extracted["precond_sound_complete"] == LeanTestScore.PASS
                and extracted["postcond_sound_complete"] == LeanTestScore.PASS
            ):
                extracted["precond_postcond"] = LeanTestScore.PASS
            else:
                extracted["precond_postcond"] = LeanTestScore.FAIL
        if "proof" in scores:
            proof_score = ProofMetricScore(**scores["proof"])
            extracted["proof"] = (
                LeanTestScore.PASS if proof_score.can_compile else LeanTestScore.FAIL
            )
        if "code" in extracted and "precond_postcond" in extracted:
            if (
                extracted["code"] == LeanTestScore.PASS
                and extracted["precond_postcond"] == LeanTestScore.PASS
            ):
                extracted["code_spec"] = LeanTestScore.PASS
            else:
                extracted["code_spec"] = LeanTestScore.FAIL
        return extracted

    @staticmethod
    def merge_score_dicts(
        score_dicts: List[Dict[str, LeanTestScore]],
    ) -> Dict[str, List[LeanTestScore]]:
        merged_scores = {}
        for score_dict in score_dicts:
            for metric, score in score_dict.items():
                if metric not in merged_scores:
                    merged_scores[metric] = []
                merged_scores[metric].append(score)
        return merged_scores

    def add_experiment_report(
        self, experiment_report: EvaluationExperimentReport
    ) -> None:
        """Add an experiment report to the summary."""
        for data_report in experiment_report.data_reports.values():
            for task_name, task_report in data_report.task_reports.items():
                if task_name not in self.results:
                    self.results[task_name] = {}
                if data_report.data_id not in self.results[task_name]:
                    self.results[task_name][data_report.data_id] = {}
                if task_name not in self.overestimate_results:
                    self.overestimate_results[task_name] = {}
                if data_report.data_id not in self.overestimate_results[task_name]:
                    self.overestimate_results[task_name][data_report.data_id] = {}

                scores = self.extract_score(task_report.scores)
                overestimate_scores = self.extract_score(
                    task_report.scores, overestimate=True
                )

                for metric, score in scores.items():
                    if metric not in self.results[task_name][data_report.data_id]:
                        self.results[task_name][data_report.data_id][metric] = []
                    self.results[task_name][data_report.data_id][metric].append(score)

                for metric, score in overestimate_scores.items():
                    if (
                        metric
                        not in self.overestimate_results[task_name][data_report.data_id]
                    ):
                        self.overestimate_results[task_name][data_report.data_id][
                            metric
                        ] = []
                    self.overestimate_results[task_name][data_report.data_id][
                        metric
                    ].append(score)

    @staticmethod
    def from_rounds_report(
        rounds_report: EvaluationRoundsReport,
    ) -> "DatapointSummaryReport":
        """Create a summary report from the rounds report."""
        summary_report = DatapointSummaryReport()
        for experiment_report in rounds_report.rounds.values():
            summary_report.add_experiment_report(experiment_report)
        return summary_report

    # returns task_name -> metric -> pass@k
    def pass_at_k(
        self,
        k: int,
        overestimate: bool = False,
        dataset: Optional[str | List[str]] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Calculate pass@k for each task and metric.
        """
        source = self.overestimate_results if overestimate else self.results
        # first, calculate pass@k for each individual datapoint
        # task_name -> data_id -> metric_name -> pass@k value
        data_results = {}
        for task_name, data_reports in source.items():
            if task_name not in data_results:
                data_results[task_name] = {}
            for data_id, metrics in data_reports.items():
                if dataset is not None:
                    if isinstance(dataset, str) and not data_id.startswith(dataset):
                        continue
                    if isinstance(dataset, list):
                        if not any(data_id.startswith(d) for d in dataset):
                            continue
                if data_id not in data_results[task_name]:
                    data_results[task_name][data_id] = {}
                for metric_name, scores in metrics.items():
                    n = len(scores)
                    c = sum(1 for score in scores if score == LeanTestScore.PASS)
                    data_results[task_name][data_id][metric_name] = pass_at_k(n, c, k)
        # then, calculate pass@k for each task and metric
        # task_name -> metric_name -> avg. pass@k value
        results = {}
        for task_name, data_reports in data_results.items():
            if task_name not in results:
                results[task_name] = {}
            for data_id, metrics in data_reports.items():
                for metric_name, pass_at_k_value in metrics.items():
                    if metric_name not in results[task_name]:
                        results[task_name][metric_name] = []
                    results[task_name][metric_name].append(pass_at_k_value)
        # calculate the average pass@k value for each task and metric
        for task_name, metrics in results.items():
            for metric_name, scores in metrics.items():
                results[task_name][metric_name] = sum(scores) / len(scores)
        return results

    # returns task_name -> metric -> pass@k
    def any_at_k(
        self,
        k: int,
        overestimate: bool = False,
        dataset: Optional[str | List[str]] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Calculate any@k for each task and metric. For example, if k=3, it only considers the first 3 rounds.
        """
        source = self.overestimate_results if overestimate else self.results
        # first, calculate any@k for each individual datapoint
        # task_name -> data_id -> metric_name -> pass@k value
        data_results = {}
        for task_name, data_reports in source.items():
            if task_name not in data_results:
                data_results[task_name] = {}
            for data_id, metrics in data_reports.items():
                if dataset is not None:
                    if isinstance(dataset, str) and not data_id.startswith(dataset):
                        continue
                    if isinstance(dataset, list):
                        if not any(data_id.startswith(d) for d in dataset):
                            continue
                if data_id not in data_results[task_name]:
                    data_results[task_name][data_id] = {}
                for metric_name, scores in metrics.items():
                    data_results[task_name][data_id][metric_name] = any(
                        score == LeanTestScore.PASS for score in scores[:k]
                    )
        # then, calculate any@k for each task and metric
        # task_name -> metric_name -> avg. any@k value
        results = {}
        for task_name, data_reports in data_results.items():
            if task_name not in results:
                results[task_name] = {}
            for data_id, metrics in data_reports.items():
                for metric_name, pass_at_k_value in metrics.items():
                    if metric_name not in results[task_name]:
                        results[task_name][metric_name] = []
                    results[task_name][metric_name].append(pass_at_k_value)
        # calculate the average any@k value for each task and metric
        for task_name, metrics in results.items():
            for metric_name, scores in metrics.items():
                results[task_name][metric_name] = sum(scores) / len(scores)
        return results
