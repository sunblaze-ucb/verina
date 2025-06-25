from typing import Any, Iterable, Optional

from prefect import task
from prefect.context import TaskRunContext
from prefect.logging import get_run_logger
from prefect.utilities.hashing import hash_objects

from verina.benchmark.common import BenchmarkRunConfig
from verina.benchmark.context import get_experiment_id
from verina.benchmark.metrics import (
    SpecMetricScore,
    metric_generated_code,
    metric_generated_proof,
    metric_generated_spec_compile,
    metric_generated_spec_unit_test_entry,
)
from verina.benchmark.report import (
    EvaluationTaskArtifact,
    EvaluationTaskFlags,
    EvaluationTaskOptions,
    EvaluationTaskReport,
)
from verina.benchmark.solution import (
    FewshotExample,
    GenCodeInput,
    GenCodeOutput,
    GenCodeProofInput,
    GenCodeProofOutput,
    GenCodeSpecInput,
    GenCodeSpecOutput,
    GenCodeSpecProofInput,
    GenCodeSpecProofOutput,
    GenProofInput,
    GenProofOutput,
    GenSpecInput,
    GenSpecOutput,
    GenSpecProofInput,
    GenSpecProofOutput,
    Solution,
    merge_imports,
)
from verina.dataset.schema import BenchmarkData
from verina.dataset.template import LeanGenerationTaskTemplate

"""
This module defines benchmark tasks.
"""


def execution_task_cache_key_fn(
    task_run_ctx: TaskRunContext,
    parameters: dict[str, Any],
) -> str:
    experiment_id = get_experiment_id()
    task_name = task_run_ctx.task.name
    solution: Solution = parameters["solution"]
    data: BenchmarkData = parameters["data"]
    fewshot_examples: Iterable[BenchmarkData] = parameters["fewshot_examples"]
    fewshot_example_names = sorted([data.data_id for data in fewshot_examples])
    fewshot_hash = hash_objects(fewshot_example_names, raise_on_failure=True)
    key = f"evaluate_E:{experiment_id}_T:{task_name}_S:{solution.cache_id()}_D:{data.data_id}_F:{fewshot_hash}"
    if "with_ref_spec" in parameters:
        with_ref_spec = parameters["with_ref_spec"]
        key += f"_O:{with_ref_spec}"
    if "with_spec_desc" in parameters:
        with_spec_desc = parameters["with_spec_desc"]
        key += f"_O:{with_spec_desc}"
    if "with_ref_code" in parameters:
        with_ref_code = parameters["with_ref_code"]
        key += f"_O:{with_ref_code}"
    return key


def benchmark_data_to_gen_code_input(
    data: BenchmarkData, with_ref_spec: bool
) -> GenCodeInput:
    if with_ref_spec:
        ref_precond_aux = data.lean_data.precond_aux
        ref_precond = data.lean_data.precond
        ref_postcond_aux = data.lean_data.postcond_aux
        ref_postcond = data.lean_data.postcond
    else:
        ref_precond_aux = None
        ref_precond = None
        ref_postcond_aux = None
        ref_postcond = None
    return GenCodeInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        ref_precond_aux=ref_precond_aux,
        ref_precond=ref_precond,
        ref_postcond_aux=ref_postcond_aux,
        ref_postcond=ref_postcond,
    )


def benchmark_data_to_gen_code_fewshot_example(
    data: BenchmarkData,
) -> FewshotExample[GenCodeInput, GenCodeOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_code_input(data, with_ref_spec=False),
        example_output=GenCodeOutput(
            imports=data.lean_data.solution_imports,
            code_aux=data.lean_data.solution_aux + "\n" + data.lean_data.code_aux,
            code=data.lean_data.code,
        ),
    )


def _execute_code_gen_task_name(with_ref_spec: bool) -> str:
    return "execute_code_gen_with_ref_spec" if with_ref_spec else "execute_code_gen"


@task(
    name="execute_code_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_code_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
    *,
    with_ref_spec: bool,
) -> EvaluationTaskReport:
    """
    Execute the code generation task from solution.
    """
    logger = get_run_logger()
    logger.info(f"Execute code generation task with ref spec: {with_ref_spec}")
    task_name = _execute_code_gen_task_name(with_ref_spec)
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_code_fewshot_examples = [
        benchmark_data_to_gen_code_fewshot_example(example)
        for example in fewshot_examples
    ]
    gen_code_input = benchmark_data_to_gen_code_input(data, with_ref_spec=with_ref_spec)
    gen_code_output = await solution.gen_code(
        data.data_id, gen_code_input, gen_code_fewshot_examples, gen_checkpoint
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_code(),
        task_options=EvaluationTaskOptions(
            with_ref_spec=with_ref_spec,
        ),
        artifact=EvaluationTaskArtifact(**gen_code_output.model_dump()),
    )


def benchmark_data_to_gen_spec_input(
    data: BenchmarkData, with_spec_desc: bool, with_ref_code: bool
) -> GenSpecInput:
    return GenSpecInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        precond_desc=data.spec_desc.precond_desc if with_spec_desc else None,
        postcond_desc=data.spec_desc.postcond_desc if with_spec_desc else None,
        ref_code_aux=data.lean_data.code_aux if with_ref_code else None,
        ref_code=data.lean_data.code if with_ref_code else None,
    )


def benchmark_data_to_gen_spec_fewshot_example(
    data: BenchmarkData,
) -> FewshotExample[GenSpecInput, GenSpecOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_spec_input(
            data, with_spec_desc=False, with_ref_code=False
        ),
        example_output=GenSpecOutput(
            imports=data.lean_data.solution_imports,
            precond_aux=data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux,
            precond=data.lean_data.precond,
            postcond_aux=data.lean_data.postcond_aux,
            postcond=data.lean_data.postcond,
        ),
    )


def _execute_spec_gen_task_name(
    with_spec_desc: bool,
    with_ref_code: bool,
) -> str:
    match (with_spec_desc, with_ref_code):
        case (True, True):
            return "execute_spec_gen_with_spec_desc_and_ref_code"
        case (True, False):
            return "execute_spec_gen_with_spec_desc"
        case (False, True):
            return "execute_spec_gen_with_ref_code"
        case (False, False):
            return "execute_spec_gen"


@task(
    name="execute_spec_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_spec_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
    *,
    with_spec_desc: bool,
    with_ref_code: bool,
) -> EvaluationTaskReport:
    """
    Execute the spec generation task from solution.
    """
    logger = get_run_logger()
    logger.info(
        f"Execute spec generation task with spec desc: {with_spec_desc}, ref code: {with_ref_code}"
    )
    task_name = _execute_spec_gen_task_name(with_spec_desc, with_ref_code)
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_spec_fewshot_examples = [
        benchmark_data_to_gen_spec_fewshot_example(example)
        for example in fewshot_examples
    ]
    gen_spec_input = benchmark_data_to_gen_spec_input(
        data, with_spec_desc=with_spec_desc, with_ref_code=with_ref_code
    )
    gen_spec_output = await solution.gen_spec(
        data.data_id, gen_spec_input, gen_spec_fewshot_examples, gen_checkpoint
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_spec(),
        task_options=EvaluationTaskOptions(
            with_spec_desc=with_spec_desc,
            with_ref_code=with_ref_code,
        ),
        artifact=EvaluationTaskArtifact(**gen_spec_output.model_dump()),
    )


def benchmark_data_to_gen_proof_input(data: BenchmarkData) -> GenProofInput:
    return GenProofInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        code_spec_imports=data.lean_data.solution_imports,
        code_aux=data.lean_data.code_aux,
        code=data.lean_data.code,
        precond_aux=data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux,
        precond=data.lean_data.precond,
        postcond_aux=data.lean_data.postcond_aux,
        postcond=data.lean_data.postcond,
    )


def benchmark_data_to_gen_proof_fewshot_example(
    data: BenchmarkData,
) -> FewshotExample[GenProofInput, GenProofOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_proof_input(data),
        example_output=GenProofOutput(
            imports=data.lean_data.solution_imports,
            proof_aux=data.lean_data.proof_aux,
            proof=data.lean_data.proof,
        ),
    )


@task(
    name="execute_proof_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_proof_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
) -> EvaluationTaskReport:
    """
    Execute the proof generation task.
    """
    logger = get_run_logger()
    logger.info("Execute proof generation task")
    task_name = "execute_proof_gen"
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_proof_fewshot_examples = [
        benchmark_data_to_gen_proof_fewshot_example(example)
        for example in fewshot_examples
    ]
    gen_proof_input = benchmark_data_to_gen_proof_input(data)
    gen_proof_output = await solution.gen_proof(
        data.data_id, gen_proof_input, gen_proof_fewshot_examples, gen_checkpoint
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_proof(),
        task_options=EvaluationTaskOptions(),
        extra_info=gen_proof_output.extra_info,
        artifact=EvaluationTaskArtifact(**gen_proof_output.model_dump()),
    )


def benchmark_data_to_gen_code_spec_input(
    data: BenchmarkData, with_spec_desc: bool
) -> GenCodeSpecInput:
    return GenCodeSpecInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        precond_desc=data.spec_desc.precond_desc if with_spec_desc else None,
        postcond_desc=data.spec_desc.postcond_desc if with_spec_desc else None,
    )


def benchmark_data_to_gen_code_spec_fewshot_example(
    data: BenchmarkData, with_spec_desc: bool
) -> FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_code_spec_input(
            data, with_spec_desc=with_spec_desc
        ),
        example_output=GenCodeSpecOutput(
            imports=data.lean_data.solution_imports,
            code_aux=data.lean_data.code_aux,
            code=data.lean_data.code,
            precond_aux=data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux,
            precond=data.lean_data.precond,
            postcond_aux=data.lean_data.postcond_aux,
            postcond=data.lean_data.postcond,
        ),
    )


def _execute_code_spec_gen_task_name(with_spec_desc: bool) -> str:
    return (
        "execute_code_spec_gen_with_spec_desc"
        if with_spec_desc
        else "execute_code_spec_gen"
    )


@task(
    name="execute_code_spec_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_code_spec_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
    *,
    with_spec_desc: bool,
) -> EvaluationTaskReport:
    """
    Execute the code and spec generation task.
    """
    logger = get_run_logger()
    logger.info(
        f"Execute code and spec generation task with spec desc: {with_spec_desc}"
    )
    task_name = _execute_code_spec_gen_task_name(with_spec_desc)
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_code_spec_fewshot_examples = [
        benchmark_data_to_gen_code_spec_fewshot_example(example, with_spec_desc)
        for example in fewshot_examples
    ]
    gen_code_spec_input = benchmark_data_to_gen_code_spec_input(
        data, with_spec_desc=with_spec_desc
    )
    gen_code_spec_output = await solution.gen_code_spec(
        data.data_id,
        gen_code_spec_input,
        gen_code_spec_fewshot_examples,
        gen_checkpoint,
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_code_spec(),
        task_options=EvaluationTaskOptions(
            with_spec_desc=with_spec_desc,
        ),
        artifact=EvaluationTaskArtifact(**gen_code_spec_output.model_dump()),
    )


def benchmark_data_to_gen_code_proof_input(
    data: BenchmarkData,
) -> GenCodeProofInput:
    return GenCodeProofInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        spec_imports=data.lean_data.solution_imports,
        precond_aux=data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux,
        precond=data.lean_data.precond,
        postcond_aux=data.lean_data.postcond_aux,
        postcond=data.lean_data.postcond,
    )


def benchmark_data_to_gen_code_proof_fewshot_example(
    data: BenchmarkData,
) -> FewshotExample[GenCodeProofInput, GenCodeProofOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_code_proof_input(data),
        example_output=GenCodeProofOutput(
            imports=data.lean_data.solution_imports,
            code_aux=data.lean_data.code_aux,
            code=data.lean_data.code,
            proof_aux=data.lean_data.proof_aux,
            proof=data.lean_data.proof,
        ),
    )


def _execute_code_proof_gen_task_name() -> str:
    return "execute_code_proof_gen"


@task(
    name="execute_code_proof_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_code_proof_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
) -> EvaluationTaskReport:
    """
    Execute the code and proof generation task.
    """
    logger = get_run_logger()
    logger.info("Execute code and proof generation task")
    task_name = _execute_code_proof_gen_task_name()
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_code_proof_fewshot_examples = [
        benchmark_data_to_gen_code_proof_fewshot_example(example)
        for example in fewshot_examples
    ]
    gen_code_proof_input = benchmark_data_to_gen_code_proof_input(data)
    gen_code_proof_output = await solution.gen_code_proof(
        data.data_id,
        gen_code_proof_input,
        gen_code_proof_fewshot_examples,
        gen_checkpoint,
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_code_proof(),
        task_options=EvaluationTaskOptions(),
        artifact=EvaluationTaskArtifact(**gen_code_proof_output.model_dump()),
    )


def benchmark_data_to_gen_spec_proof_input(
    data: BenchmarkData, with_spec_desc: bool
) -> GenSpecProofInput:
    return GenSpecProofInput(
        description=data.description,
        signature=data.signature,
        task_imports=data.lean_data.task_imports,
        task_aux=data.lean_data.task_aux,
        code_imports=data.lean_data.solution_imports,
        code_aux=data.lean_data.solution_aux + "\n" + data.lean_data.code_aux,
        code=data.lean_data.code,
        precond_desc=data.spec_desc.precond_desc if with_spec_desc else None,
        postcond_desc=data.spec_desc.postcond_desc if with_spec_desc else None,
    )


def benchmark_data_to_gen_spec_proof_fewshot_example(
    data: BenchmarkData, with_spec_desc: bool
) -> FewshotExample[GenSpecProofInput, GenSpecProofOutput]:
    return FewshotExample(
        example_input=benchmark_data_to_gen_spec_proof_input(
            data, with_spec_desc=with_spec_desc
        ),
        example_output=GenSpecProofOutput(
            imports=data.lean_data.solution_imports,
            precond_aux=data.lean_data.precond_aux,
            precond=data.lean_data.precond,
            postcond_aux=data.lean_data.postcond_aux,
            postcond=data.lean_data.postcond,
            proof_aux=data.lean_data.proof_aux,
            proof=data.lean_data.proof,
        ),
    )


def _execute_spec_proof_gen_task_name(with_spec_desc: bool) -> str:
    return (
        "execute_spec_proof_gen_with_spec_desc"
        if with_spec_desc
        else "execute_spec_proof_gen"
    )


@task(
    name="execute_spec_proof_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_spec_proof_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
    *,
    with_spec_desc: bool,
) -> EvaluationTaskReport:
    """
    Execute the spec and proof generation task.
    """
    logger = get_run_logger()
    logger.info(
        f"Execute spec and proof generation task with spec desc: {with_spec_desc}"
    )
    task_name = _execute_spec_proof_gen_task_name(with_spec_desc)
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_spec_proof_fewshot_examples = [
        benchmark_data_to_gen_spec_proof_fewshot_example(example, with_spec_desc)
        for example in fewshot_examples
    ]
    gen_spec_proof_input = benchmark_data_to_gen_spec_proof_input(
        data, with_spec_desc=with_spec_desc
    )
    gen_spec_proof_output = await solution.gen_spec_proof(
        data.data_id,
        gen_spec_proof_input,
        gen_spec_proof_fewshot_examples,
        gen_checkpoint,
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_spec_proof(),
        task_options=EvaluationTaskOptions(
            with_spec_desc=with_spec_desc,
        ),
        artifact=EvaluationTaskArtifact(**gen_spec_proof_output.model_dump()),
    )


def benchmark_data_to_gen_code_spec_proof_fewshot_example(
    data: BenchmarkData,
    with_spec_desc: bool,
) -> FewshotExample[GenCodeSpecProofInput, GenCodeSpecProofOutput]:
    proof = data.lean_data.proof if "sorry" not in data.lean_data.proof else ""
    return FewshotExample(
        example_input=benchmark_data_to_gen_code_spec_input(
            data, with_spec_desc=with_spec_desc
        ),
        example_output=GenCodeSpecProofOutput(
            imports=data.lean_data.solution_imports,
            code_aux=data.lean_data.code_aux,
            code=data.lean_data.code,
            precond_aux=data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux,
            precond=data.lean_data.precond,
            postcond_aux=data.lean_data.postcond_aux,
            postcond=data.lean_data.postcond,
            proof_aux=data.lean_data.proof_aux,
            proof=proof,
        ),
    )


def _execute_code_spec_proof_gen_task_name(with_spec_desc: bool) -> str:
    return (
        "execute_code_spec_proof_gen_with_spec_desc"
        if with_spec_desc
        else "execute_code_spec_proof_gen"
    )


@task(
    name="execute_code_spec_proof_gen",
    cache_key_fn=execution_task_cache_key_fn,
    retries=3,
    retry_delay_seconds=[1, 10, 100],
)
async def execute_code_spec_proof_gen(
    solution: Solution,
    data: BenchmarkData,
    fewshot_examples: Iterable[BenchmarkData],
    checkpoint: Optional[EvaluationTaskReport],
    *,
    with_spec_desc: bool,
) -> EvaluationTaskReport:
    """
    Execute the code, spec, and proof generation task.
    """
    logger = get_run_logger()
    logger.info(
        f"Execute code, spec, and proof generation task with spec desc: {with_spec_desc}"
    )
    task_name = _execute_code_spec_proof_gen_task_name(with_spec_desc)
    fewshot_example_names = [example.data_id for example in fewshot_examples]

    gen_checkpoint = checkpoint.artifact if checkpoint else None

    # Generation
    gen_code_spec_proof_fewshot_examples = [
        benchmark_data_to_gen_code_spec_proof_fewshot_example(example, with_spec_desc)
        for example in fewshot_examples
    ]
    # The input examlple transformation is the same as code-spec generation
    gen_code_spec_proof_input = benchmark_data_to_gen_code_spec_input(
        data, with_spec_desc=with_spec_desc
    )
    gen_code_spec_proof_output = await solution.gen_code_spec_proof(
        data.data_id,
        gen_code_spec_proof_input,
        gen_code_spec_proof_fewshot_examples,
        gen_checkpoint,
    )

    # Report
    return EvaluationTaskReport(
        task_name=task_name,
        data_id=data.data_id,
        fewshot_example_names=fewshot_example_names,
        task_flags=EvaluationTaskFlags.gen_code_spec_proof(),
        task_options=EvaluationTaskOptions(
            with_spec_desc=with_spec_desc,
        ),
        artifact=EvaluationTaskArtifact(**gen_code_spec_proof_output.model_dump()),
    )


@task(name="evaluate_task_from_report", retries=3, retry_delay_seconds=1)
async def evaluate_task_from_report(
    config: BenchmarkRunConfig,
    data: BenchmarkData,
    task_report: EvaluationTaskReport,
    should_reevaluate: bool = True,
) -> EvaluationTaskReport:
    """
    Evaluate the artifact from task report and update the score.
    """
    if task_report.data_id != data.data_id:
        raise ValueError(
            f"Task report data name {task_report.data_id} does not match data id {data.data_id}"
        )

    template_engine = LeanGenerationTaskTemplate(data.signature)
    scores = task_report.scores

    imports = data.lean_data.solution_imports
    if task_report.artifact.imports:
        imports = merge_imports(
            [
                imports,
                task_report.artifact.imports,
            ]
        )

    if task_report.task_flags.code and ("code" not in scores or should_reevaluate):
        # Evaluate code
        code_artifact = task_report.artifact.model_copy()
        # We always use the ground truth precondition to evaluate the generated code
        code_artifact.precond_aux = (
            data.lean_data.solution_aux + "\n" + data.lean_data.precond_aux
        )
        code_artifact.precond = data.lean_data.precond
        scores["code"] = await metric_generated_code(
            template_engine,
            data,
            code_artifact,
        )
    if task_report.task_flags.spec:
        # Evaluate spec
        # TODO: currently spec is always evaluated, not following `should_reevaluate`
        for eval_type in ["precond", "postcond"]:
            assert (
                eval_type == "precond" or eval_type == "postcond"
            )  # make pyright happy
            if eval_type not in scores:
                scores[eval_type] = await metric_generated_spec_compile(
                    None,
                    template_engine,
                    data,
                    task_report.artifact,
                    eval_type,
                )
            elif isinstance(scores[eval_type], dict):
                scores[eval_type] = SpecMetricScore.model_validate(scores[eval_type])
            if scores[eval_type].can_compile:
                if config.eval_spec_config.unit_test:
                    scores[eval_type] = await metric_generated_spec_unit_test_entry(
                        scores[eval_type],
                        config.eval_spec_config,
                        template_engine,
                        data,
                        task_report.artifact,
                        eval_type,
                    )
    if task_report.task_flags.proof and ("proof" not in scores or should_reevaluate):
        # Evaluate proof
        proof_artifact = task_report.artifact.model_copy()
        if not task_report.task_flags.code and not task_report.task_flags.spec:
            # If the task does not generate code or spec, we need to evaluate using the ground truth
            gen_proof_input = benchmark_data_to_gen_proof_input(data)
            proof_artifact.code_aux = gen_proof_input.code_aux
            proof_artifact.code = gen_proof_input.code
            proof_artifact.precond_aux = (
                data.lean_data.solution_aux + "\n" + gen_proof_input.precond_aux
            )
            proof_artifact.precond = gen_proof_input.precond
            proof_artifact.postcond_aux = gen_proof_input.postcond_aux
            proof_artifact.postcond = gen_proof_input.postcond

        scores["proof"] = await metric_generated_proof(
            template_engine, data, proof_artifact
        )

    task_report.scores = scores
    return task_report
