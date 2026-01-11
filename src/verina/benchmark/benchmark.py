import asyncio
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, cast

from prefect import flow, task
from prefect.context import TaskRunContext
from prefect.futures import wait
from prefect.logging import get_run_logger
from prefect.task_runners import ThreadPoolTaskRunner
from prefect.transactions import CommitMode, transaction
from prefect.utilities.annotations import quote
from prefect.utilities.hashing import hash_objects

from verina.benchmark.common import (
    BenchmarkRunConfig,
    ExperimentId,
    TaskId,
)
from verina.benchmark.context import BenchmarkContext, get_experiment_id
from verina.benchmark.evaluation_tasks import (
    EvaluationTaskArtifact,
    EvaluationTaskFlags,
    EvaluationTaskOptions,
    EvaluationTaskReport,
    evaluate_task_from_report,
    execute_code_gen,
    execute_code_proof_gen,
    execute_code_spec_gen,
    execute_code_spec_proof_gen,
    execute_proof_gen,
    execute_spec_gen,
    execute_spec_proof_gen,
)
from verina.benchmark.report import (
    EvaluationDataReport,
    EvaluationExperimentReport,
    EvaluationRoundsReport,
)
from verina.benchmark.solution import Solution
from verina.dataset.schema import BenchmarkData


def generate_datapoint_cache_key_fn(
    task_run_ctx: TaskRunContext,
    parameters: dict[str, Any],
) -> str:
    experiment_id = get_experiment_id()
    solution: Solution = parameters["solution"]
    data: BenchmarkData = parameters["data"]
    fewshot_examples: Iterable[BenchmarkData] = parameters["fewshot_examples"]
    fewshot_example_names = sorted([data.data_id for data in fewshot_examples])
    fewshot_hash = hash_objects(fewshot_example_names, raise_on_failure=True)
    return f"generate_E:{experiment_id}_S:{solution.cache_id()}_D:{data.data_id}_F:{fewshot_hash}"


def evaluate_datapoint_cache_key_fn(
    task_run_ctx: TaskRunContext,
    parameters: dict[str, Any],
) -> str:
    experiment_id = get_experiment_id()
    data: BenchmarkData = parameters["data"]
    return f"evaluate_E:{experiment_id}_D:{data.data_id}"


def get_task_checkpoint_from_report(
    existing_report: Optional[Dict[TaskId, EvaluationTaskReport]], task_name: str
) -> Optional[EvaluationTaskReport]:
    if existing_report is not None:
        return existing_report.get(TaskId(task_name))
    return None


class Benchmark:
    def __init__(self, config: BenchmarkRunConfig):
        self.config = config

    # TODO: TASK_SOURCE should be in cache key as well
    @task(
        cache_key_fn=generate_datapoint_cache_key_fn,
    )
    async def generate_datapoint(
        self,
        solution: Solution,
        data: BenchmarkData,
        fewshot_examples: Iterable[BenchmarkData],
        existing_report: Optional[Dict[TaskId, EvaluationTaskReport]] = None,
    ) -> Dict[TaskId, EvaluationTaskReport]:
        logger = get_run_logger()
        logger.info(f"Running generation for {solution.name()} on {data.data_id}")

        # TODO: disabled specification description usage for now

        # Use quote to prevent Prefect from introspecting the task and disable dependancy tracking
        # since we know these tasks won't depend on each other
        solution = cast(Solution, quote(solution))
        data = cast(BenchmarkData, quote(data))
        fewshot_examples = cast(Iterable[BenchmarkData], quote(fewshot_examples))

        # We can't submit these tasks to prefect because they will cause starvation
        # as this function runs in a separate thread already
        futures = {}

        existing_report = existing_report or {}
        itp_type = self.config.get_itp_type()

        # Only run tasks that are enabled in the configuration
        if self.config.code_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_code_gen"
            )
            futures["code_gen"] = execute_code_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                with_ref_spec=False,
                itp_type=itp_type,
                return_state=False,
            )

        if self.config.spec_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_spec_gen"
            )
            futures["spec_gen"] = execute_spec_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                with_ref_code=False,
                with_spec_desc=False,
                itp_type=itp_type,
                return_state=False,
            )

        if self.config.proof_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_proof_gen"
            )
            futures["proof_gen"] = execute_proof_gen(
                solution, data, fewshot_examples, checkpoint, itp_type=itp_type, return_state=False
            )

        if self.config.code_spec_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_code_spec_gen"
            )
            futures["code_spec_gen"] = execute_code_spec_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                with_spec_desc=False,
                return_state=False,
            )

        if self.config.code_proof_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_code_proof_gen"
            )
            futures["code_proof_gen"] = execute_code_proof_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                return_state=False,
            )

        if self.config.spec_proof_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_spec_proof_gen"
            )
            futures["spec_proof_gen"] = execute_spec_proof_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                with_spec_desc=False,
                return_state=False,
            )

        if self.config.code_spec_proof_gen:
            checkpoint = get_task_checkpoint_from_report(
                existing_report, "execute_code_spec_proof_gen"
            )
            futures["code_spec_proof_gen"] = execute_code_spec_proof_gen(
                solution,
                data,
                fewshot_examples,
                checkpoint,
                with_spec_desc=False,
                return_state=False,
            )

        results = await asyncio.gather(*futures.values())
        task_reports = {result.task_name: result for result in results}
        return task_reports

    # TODO: TASK_SOURCE should be in cache key as well
    @task(
        cache_key_fn=evaluate_datapoint_cache_key_fn,
    )
    async def evaluate_datapoint(
        self,
        data: BenchmarkData,
        task_reports: Dict[TaskId, EvaluationTaskReport],
        should_reevaluate: bool = True,
    ) -> Dict[TaskId, EvaluationTaskReport]:
        logger = get_run_logger()
        logger.info(f"Running evaluation on {data.data_id}")

        # Use quote to prevent Prefect from introspecting the task and disable dependancy tracking
        # since we know these tasks won't depend on each other
        data = cast(BenchmarkData, quote(data))

        futures = {}

        for task_name, task_report in task_reports.items():
            task_report = cast(EvaluationTaskReport, quote(task_report))
            futures[task_name] = evaluate_task_from_report(
                self.config, data, task_report, should_reevaluate
            )

        results = await asyncio.gather(*futures.values())
        task_reports = {result.task_name: result for result in results}
        return task_reports

    async def _benchmark(
        self,
        experiment_id: ExperimentId,
        solution: Solution,
        dataset: List[BenchmarkData],
        fewshot_examples: List[BenchmarkData],
        existing_report: Optional[EvaluationExperimentReport] = None,
        should_reevaluate: bool = True,
    ) -> EvaluationExperimentReport:
        from verina.itp import ITPType
        from verina.benchmark.metrics import set_compiler_config

        logger = get_run_logger()
        logger.info(f"Running evaluation for {solution.name()} on {experiment_id}")

        # Set compiler config for Coq (e.g., docker_image for QuickChick)
        itp_type = self.config.get_itp_type()
        if itp_type == ITPType.COQ and self.config.coq_config:
            if self.config.coq_config.docker_image:
                set_compiler_config(
                    ITPType.COQ,
                    docker_image=self.config.coq_config.docker_image
                )
                logger.info(f"Using Docker image: {self.config.coq_config.docker_image}")

        with (
            BenchmarkContext(experiment_id=experiment_id),
            transaction(commit_mode=CommitMode.EAGER),
        ):
            fewshot_example_names = [example.data_id for example in fewshot_examples]
            evaluation_dataset = [
                data for data in dataset if data.data_id not in fewshot_example_names
            ]
            evaluation_dataset_map = {data.data_id: data for data in evaluation_dataset}

            if self.config.run_type == "evaluate_only":
                # Load report from output directory
                assert existing_report is not None, (
                    "Existing report must be provided for evaluate_only run type"
                )
                raw_data_reports = existing_report.data_reports.values()
            else:
                # Generate report from potential checkpoint
                # Submit generation tasks for each datapoint
                data_report_futures = []
                for data in evaluation_dataset:
                    task_reports = None
                    if existing_report is not None:
                        data_report = existing_report.data_reports.get(data.data_id)
                        if data_report is not None:
                            task_reports = data_report.task_reports
                    data_report_futures.append(
                        self.generate_datapoint.submit(
                            solution,
                            data,
                            fewshot_examples,
                            task_reports,
                            return_state=False,
                        )
                    )

                # Wait for all tasks to complete
                wait(data_report_futures)
                raw_data_reports = [
                    EvaluationDataReport.parse_dict(future.result())
                    for future in data_report_futures
                ]

            if self.config.run_type == "generate_only":
                # If we are only generating, we don't need to evaluate
                data_reports = raw_data_reports
            else:
                # Submit evaluation tasks for each task report
                eval_func = self.evaluate_datapoint
                if should_reevaluate:
                    eval_func = eval_func.with_options(refresh_cache=True)
                data_report_futures = []
                for data_report in raw_data_reports:
                    if data_report.data_id not in evaluation_dataset_map:
                        # Skip if the data report is not in the evaluation dataset
                        continue
                    data_report_futures.append(
                        eval_func.submit(
                            evaluation_dataset_map[data_report.data_id],
                            data_report.task_reports,
                            should_reevaluate,
                            return_state=False,
                        )
                    )
                wait(data_report_futures)
                data_reports = [
                    EvaluationDataReport.parse_dict(future.result())
                    for future in data_report_futures
                ]

            return EvaluationExperimentReport(
                experiment_id=str(experiment_id),
                data_reports={report.data_id: report for report in data_reports},
            )

    async def _run_quality_assurance(
        self,
        experiment_id: ExperimentId,
        dataset: List[BenchmarkData],
    ):
        from verina.itp import ITPType
        from verina.benchmark.metrics import set_compiler_config

        logger = get_run_logger()
        logger.info(f"Running quality assurance on {experiment_id}")

        itp_type = self.config.get_itp_type()
        logger.info(f"Using ITP type: {itp_type}")

        # Set compiler config for Coq (e.g., docker_image for QuickChick)
        if itp_type == ITPType.COQ and self.config.coq_config:
            if self.config.coq_config.docker_image:
                set_compiler_config(
                    ITPType.COQ,
                    docker_image=self.config.coq_config.docker_image
                )
                logger.info(f"Using Docker image: {self.config.coq_config.docker_image}")

        with (
            BenchmarkContext(experiment_id=experiment_id),
            transaction(commit_mode=CommitMode.EAGER),
        ):
            dataset_map = {data.data_id: data for data in dataset}

            # Phase 1: transform dataset into evaluation data reports
            raw_data_reports = []
            for data in dataset:
                # Select appropriate data based on ITP type
                if itp_type == ITPType.COQ:
                    if data.coq_data is None:
                        logger.warning(f"Skipping {data.data_id}: no Coq data available")
                        continue
                    itp_data = data.coq_data
                    # Coq uses 'admit.' as cheat code
                    cheat_codes = ["admit", "Admitted", "Abort"]
                else:
                    itp_data = data.lean_data
                    # Lean uses 'sorry' as cheat code
                    cheat_codes = ["sorry"]

                artifact = EvaluationTaskArtifact(
                    imports=itp_data.solution_imports,
                    code_aux=itp_data.code_aux,
                    code=itp_data.code,
                    precond_aux=itp_data.solution_aux
                    + "\n"
                    + itp_data.precond_aux,
                    precond=itp_data.precond,
                    postcond_aux=itp_data.postcond_aux,
                    postcond=itp_data.postcond,
                    proof_aux=itp_data.proof_aux,
                    proof=itp_data.proof,
                )
                task_flags = EvaluationTaskFlags(
                    code=True,
                    spec=True,
                    proof=True,
                )
                # Check for cheat codes in proof
                if any(cheat in itp_data.proof for cheat in cheat_codes):
                    task_flags.proof = False
                raw_data_reports.append(
                    EvaluationDataReport(
                        data_id=data.data_id,
                        task_reports={
                            "execute_code_spec_proof_gen": EvaluationTaskReport(
                                task_name="execute_code_spec_proof_gen",
                                data_id=data.data_id,
                                fewshot_example_names=[],
                                task_flags=task_flags,
                                task_options=EvaluationTaskOptions(),
                                artifact=artifact,
                            )
                        },
                    )
                )

            # Phase 2: evaluation
            # Submit evaluation tasks for each task report
            # always refresh cache for quality assurance
            data_report_futures = []
            for data_report in raw_data_reports:
                data_report_futures.append(
                    self.evaluate_datapoint.with_options(refresh_cache=True).submit(
                        dataset_map[data_report.data_id],
                        data_report.task_reports,
                        True,
                        return_state=False,
                    )
                )
            wait(data_report_futures)
            data_reports = [
                EvaluationDataReport.parse_dict(future.result())
                for future in data_report_futures
            ]

            report = EvaluationExperimentReport(
                experiment_id=str(experiment_id),
                data_reports={report.data_id: report for report in data_reports},
            )

            output_dir = Path(str(experiment_id))
            EvaluationRoundsReport(
                config=self.config,
                rounds={0: report},
            ).save(output_dir)

    # Workaround for injecting config into flow
    @property
    # def evaluate(self) -> Flow[Concatenate[ExperimentId, Solution, Iterable[BenchmarkData], Iterable[BenchmarkData], P], Dict[InputId, dict[TaskId, bool]]]:
    def benchmark(self):
        return flow(task_runner=ThreadPoolTaskRunner(self.config.max_workers))(  # type: ignore # FIXME: weird prefect typing
            self._benchmark
        )

    # Workaround for injecting config into flow
    @property
    def run_quality_assurance(self):
        return flow(task_runner=ThreadPoolTaskRunner(self.config.max_workers))(  # type: ignore # FIXME: weird prefect typing
            self._run_quality_assurance
        )

    # This is a parent flow of all evaluation flows sequentially
    @flow
    async def benchmark_multi_round(
        self,
        experiment_id: ExperimentId,
        total_rounds: int,
        solution: Solution,
        dataset: List[BenchmarkData],
        fewshot_examples: List[BenchmarkData],
        existing_report: Optional[EvaluationRoundsReport] = None,
    ) -> EvaluationRoundsReport:
        """
        Run multiple rounds of evaluation and aggregate the results.

        Returns:
            EvaluationRoundsReport:
                - All individual round reports
        """
        logger = get_run_logger()
        experiment_reports: Dict[int, EvaluationExperimentReport] = {}

        generation_timestamp = (
            existing_report.generation_timestamp if existing_report else 0
        )
        evaluatated_version_timestamp = (
            existing_report.evaluated_version_timestamp if existing_report else 0
        )
        evaluation_timestamp = (
            existing_report.evaluation_timestamp if existing_report else 0
        )

        should_reevaluate = True

        if existing_report is not None:
            experiment_reports = existing_report.rounds
            if evaluatated_version_timestamp != generation_timestamp:
                # If the evaluated version timestamp is different from the generation timestamp,
                # we need to re-evaluate the rounds
                should_reevaluate = False

        for round_idx in range(total_rounds):
            # Generate round-specific experiment ID
            round_experiment_id = (
                experiment_id
                if round_idx == 0
                else ExperimentId(f"{experiment_id}_round{round_idx}")
            )

            logger.info(f"Benchmarking round {round_idx} for {solution.name()}")
            experiment_report = await self.benchmark(
                round_experiment_id,
                solution,
                dataset,
                fewshot_examples,
                experiment_reports.get(round_idx),
                should_reevaluate,
            )
            experiment_reports[round_idx] = experiment_report
            logger.info(f"Round {round_idx} completed")

        current_timestamp = int(datetime.now().timestamp())
        if self.config.run_type == "generate_only":
            generation_timestamp = current_timestamp
        elif self.config.run_type == "evaluate_only" or self.config.run_type == "qa":
            evaluatated_version_timestamp = generation_timestamp
            evaluation_timestamp = current_timestamp
        else:
            generation_timestamp = current_timestamp
            evaluatated_version_timestamp = current_timestamp
            evaluation_timestamp = current_timestamp

        rounds_report = EvaluationRoundsReport(
            config=self.config,
            rounds=experiment_reports,
            generation_timestamp=generation_timestamp,
            evaluation_timestamp=evaluation_timestamp,
            evaluated_version_timestamp=evaluatated_version_timestamp,
        )

        output_dir = Path(self.config.output_dir)
        rounds_report.save(output_dir)

        return rounds_report
