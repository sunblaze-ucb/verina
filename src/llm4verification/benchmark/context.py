from contextvars import ContextVar
from typing import Any, ClassVar, Optional

from prefect.cache_policies import CachePolicy
from prefect.context import ContextModel, TaskRunContext
from typing_extensions import Self

from llm4verification.benchmark.common import ExperimentId


class BenchmarkContext(ContextModel):
    __var__: ClassVar[ContextVar[Self]] = ContextVar("benchmark_context")
    experiment_id: ExperimentId


def get_experiment_id() -> Optional[ExperimentId]:
    ctx = BenchmarkContext.get()
    return ctx.experiment_id if ctx else None


def experiment_id_cache_key_fn(
    _task_run_ctx: TaskRunContext,
    _parameters: dict[str, Any],
) -> str:
    experiment_id = get_experiment_id()
    if experiment_id is None:
        raise ValueError("experiment id is not set in the context")
    return f"experiment_id:{experiment_id}"


CACHE_EXPERIMENT_ID = CachePolicy.from_cache_key_fn(experiment_id_cache_key_fn)
