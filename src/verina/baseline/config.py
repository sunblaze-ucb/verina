from typing import Literal, Optional

from pydantic import BaseModel


class BaselineConfig(BaseModel):
    name: str = "baseline"
    combind_task_preference: Literal[
        "NO_GENERATED_AS_REF", "USE_GENERATED_CODE_AS_REF", "USE_GENERATED_SPEC_AS_REF"
    ] = "NO_GENERATED_AS_REF"
    resume_from_checkpoint: bool = False
    refinements: Optional[int] = None
    dspy_module: Optional[str] = None
    custom_prompt_template: Optional[str] = None
