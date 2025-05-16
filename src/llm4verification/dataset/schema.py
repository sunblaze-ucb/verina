from typing import Any, Dict, List, Optional

from pydantic import BaseModel, Field, Json
from rich import print

from llm4verification.dataset.parsing import BenchmarkLeanData


class Parameter(BaseModel):
    param_name: str = Field(description="The name of the parameter")
    param_type: str = Field(description="The type of the parameter")


class Signature(BaseModel):
    name: str = Field(description="The name of the function")
    parameters: List[Parameter] = Field(
        default_factory=list, description="The parameters of the function"
    )
    return_type: str = Field(description="The return type of the function")


class RejectInput(BaseModel):
    input: Dict[str, Any] = Field(description="The input values for the test case")


class TestCase(BaseModel):
    input: Dict[str, Any] = Field(description="The input values for the test case")
    expected: Any = Field(description="The expected output for the test case")
    unexpected: List[Any] = Field(
        default_factory=list,
        description="The unexpected output values for the test case",
    )


class SpecDesc(BaseModel):
    precond_desc: str = Field(
        description="The natural language description of the precondition",
    )

    postcond_desc: str = Field(
        description="The natural language description of the postcondition",
    )


class BenchmarkData(BaseModel):
    data_id: str = Field(
        description="The id of the benchmark data",
    )

    description: str = Field(
        description="The natural language description of the programming task",
    )

    signature: Signature = Field(
        description="The implementation function signature that defines the type of inputs and outputs",
    )

    lean_data: BenchmarkLeanData = Field(
        description="The lean data that contains the imports, auxiliary code, and the solution",
    )

    spec_desc: SpecDesc = Field(
        description="The natural language description of the precondition and postcondition",
    )

    reject_inputs: List[RejectInput] = Field(
        description="A list of inputs that should be rejected by the implementation",
    )

    tests: List[TestCase] = Field(
        description="A list of test cases that cover the different possible behaviors of the implementation",
    )

    metadata: Optional[Json[Any]] = Field(None, description="The metadata")


if __name__ == "__main__":
    print(BenchmarkData.model_json_schema())
