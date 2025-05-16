import inspect
from abc import ABC, abstractmethod
from enum import Enum
from functools import cache
from typing import Any, Dict, Generic, List, Optional, TypeVar

from prefect.utilities.hashing import hash_objects
from pydantic import BaseModel, Field

from llm4verification.benchmark.report import EvaluationTaskArtifact
from llm4verification.dataset.schema import Signature

# TODO: make the input/output composable


class CommonInput(BaseModel):
    description: str
    signature: Signature
    task_imports: str
    task_aux: str


class GenCodeInput(CommonInput):
    ref_precond_aux: Optional[str]
    ref_precond: Optional[str]
    ref_postcond_aux: Optional[str]
    ref_postcond: Optional[str]


class GenCodeOutput(BaseModel):
    imports: str
    code_aux: str
    code: str


class GenSpecInput(CommonInput):
    precond_desc: Optional[str]
    postcond_desc: Optional[str]
    ref_code_aux: Optional[str]
    ref_code: Optional[str]


class GenSpecOutput(BaseModel):
    imports: str
    precond_aux: str
    precond: str
    postcond_aux: str
    postcond: str


class GenProofInput(CommonInput):
    code_spec_imports: str
    code_aux: str
    code: str
    precond_aux: str
    precond: str
    postcond_aux: str
    postcond: str


class GenProofOutput(BaseModel):
    imports: str
    proof_aux: str
    proof: str

    extra_info: Dict[str, Any] = Field(default_factory=dict)


class GenCodeSpecInput(CommonInput):
    precond_desc: Optional[str]
    postcond_desc: Optional[str]


class GenCodeSpecOutput(BaseModel):
    imports: str
    code_aux: str
    code: str
    precond_aux: str
    precond: str
    postcond_aux: str
    postcond: str


class GenCodeProofInput(CommonInput):
    spec_imports: str
    precond_aux: str
    precond: str
    postcond_aux: str
    postcond: str


class GenCodeProofOutput(BaseModel):
    imports: str
    code_aux: str
    code: str
    proof_aux: str
    proof: str


class GenSpecProofInput(CommonInput):
    code_imports: str
    code_aux: str
    code: str
    precond_desc: Optional[str]
    postcond_desc: Optional[str]


class GenSpecProofOutput(BaseModel):
    imports: str
    precond_aux: str
    precond: str
    postcond_aux: str
    postcond: str
    proof_aux: str
    proof: str


GenCodeSpecProofInput = GenCodeSpecInput


class GenCodeSpecProofOutput(GenCodeSpecOutput):
    proof_aux: str
    proof: str


TIn = TypeVar("TIn")
TOut = TypeVar("TOut")


class FewshotExample(BaseModel, Generic[TIn, TOut]):
    example_input: TIn
    example_output: TOut


class Solution(ABC):
    @staticmethod
    @abstractmethod
    def name() -> str:
        raise NotImplementedError

    @abstractmethod
    async def gen_code(
        self,
        data_id: str,
        input: GenCodeInput,
        fewshot_examples: List[FewshotExample[GenCodeInput, GenCodeOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_spec(
        self,
        data_id: str,
        input: GenSpecInput,
        fewshot_examples: List[FewshotExample[GenSpecInput, GenSpecOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenSpecOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_proof(
        self,
        data_id: str,
        input: GenProofInput,
        fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenProofOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_code_spec(
        self,
        data_id: str,
        input: GenCodeSpecInput,
        fewshot_examples: List[FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeSpecOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_code_proof(
        self,
        data_id: str,
        input: GenCodeProofInput,
        fewshot_examples: List[FewshotExample[GenCodeProofInput, GenCodeProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeProofOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_spec_proof(
        self,
        data_id: str,
        input: GenSpecProofInput,
        fewshot_examples: List[FewshotExample[GenSpecProofInput, GenSpecProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenSpecProofOutput:
        raise NotImplementedError

    @abstractmethod
    async def gen_code_spec_proof(
        self,
        data_id: str,
        input: GenCodeSpecProofInput,
        fewshot_examples: List[
            FewshotExample[GenCodeSpecProofInput, GenCodeSpecProofOutput]
        ],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeSpecProofOutput:
        raise NotImplementedError

    ### Utility functions

    @classmethod
    @cache
    def cache_id(cls) -> str:
        source_hash = hash_objects(inspect.getsource(cls), raise_on_failure=True)
        return f"{cls.name()}-{source_hash}"


def merge_imports(
    imports: List[str],
) -> str:
    """Merge imports into a single string and remove duplicated lines."""
    import_lines = [
        line.strip() for imp in imports for line in imp.splitlines() if line.strip()
    ]
    import_lines = list(set(import_lines))
    return "\n".join(import_lines)


def transform_codespec_to_code_fewshot_examples(
    examples: List[FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]],
    add_ref_spec_to_example: bool,
) -> List[FewshotExample[GenCodeInput, GenCodeOutput]]:
    if add_ref_spec_to_example:
        return [
            FewshotExample(
                example_input=GenCodeInput(
                    description=example.example_input.description,
                    signature=example.example_input.signature,
                    task_imports=example.example_input.task_imports,
                    task_aux=example.example_input.task_aux,
                    ref_precond_aux=example.example_output.precond_aux,
                    ref_precond=example.example_output.precond,
                    ref_postcond_aux=example.example_output.postcond_aux,
                    ref_postcond=example.example_output.postcond,
                ),
                example_output=GenCodeOutput(
                    imports=example.example_output.imports,
                    code_aux=example.example_output.code_aux,
                    code=example.example_output.code,
                ),
            )
            for example in examples
        ]
    return [
        FewshotExample(
            example_input=GenCodeInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=example.example_input.task_imports,
                task_aux=example.example_input.task_aux,
                ref_precond_aux=None,
                ref_precond=None,
                ref_postcond_aux=None,
                ref_postcond=None,
            ),
            example_output=GenCodeOutput(
                imports=example.example_output.imports,
                code_aux=example.example_output.code_aux,
                code=example.example_output.code,
            ),
        )
        for example in examples
    ]


def transform_codespec_to_spec_fewshot_examples(
    examples: List[FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]],
    add_ref_code_to_example: bool,
) -> List[FewshotExample[GenSpecInput, GenSpecOutput]]:
    if add_ref_code_to_example:
        return [
            FewshotExample(
                example_input=GenSpecInput(
                    description=example.example_input.description,
                    signature=example.example_input.signature,
                    task_imports=example.example_input.task_imports,
                    task_aux=example.example_input.task_aux,
                    precond_desc=example.example_input.precond_desc,
                    postcond_desc=example.example_input.postcond_desc,
                    ref_code_aux=example.example_output.code_aux,
                    ref_code=example.example_output.code,
                ),
                example_output=GenSpecOutput(
                    imports=example.example_output.imports,
                    precond_aux=example.example_output.precond_aux,
                    precond=example.example_output.precond,
                    postcond_aux=example.example_output.postcond_aux,
                    postcond=example.example_output.postcond,
                ),
            )
            for example in examples
        ]
    return [
        FewshotExample(
            example_input=GenSpecInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=example.example_input.task_imports,
                task_aux=example.example_input.task_aux,
                precond_desc=example.example_input.precond_desc,
                postcond_desc=example.example_input.postcond_desc,
                ref_code_aux=None,
                ref_code=None,
            ),
            example_output=GenSpecOutput(
                imports=example.example_output.imports,
                precond_aux=example.example_output.precond_aux,
                precond=example.example_output.precond,
                postcond_aux=example.example_output.postcond_aux,
                postcond=example.example_output.postcond,
            ),
        )
        for example in examples
    ]


def transform_codeproof_to_code_fewshot_examples(
    examples: List[FewshotExample[GenCodeProofInput, GenCodeProofOutput]],
) -> List[FewshotExample[GenCodeInput, GenCodeOutput]]:
    # In codeproof task, by default we have the ref precond and postcond
    return [
        FewshotExample(
            example_input=GenCodeInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=merge_imports(
                    [
                        example.example_input.task_imports,
                        example.example_input.spec_imports,
                    ]
                ),
                task_aux=example.example_input.task_aux,
                ref_precond_aux=example.example_input.precond_aux,
                ref_precond=example.example_input.precond,
                ref_postcond_aux=example.example_input.postcond_aux,
                ref_postcond=example.example_input.postcond,
            ),
            example_output=GenCodeOutput(
                imports=example.example_output.imports,
                code_aux=example.example_output.code_aux,
                code=example.example_output.code,
            ),
        )
        for example in examples
    ]


def transform_codeproof_to_proof_fewshot_examples(
    examples: List[FewshotExample[GenCodeProofInput, GenCodeProofOutput]],
) -> List[FewshotExample[GenProofInput, GenProofOutput]]:
    return [
        FewshotExample(
            example_input=GenProofInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=merge_imports(
                    [
                        example.example_input.task_imports,
                        example.example_input.spec_imports,
                    ]
                ),
                task_aux=example.example_input.task_aux,
                code_spec_imports=example.example_output.imports,
                code_aux=example.example_output.code_aux,
                code=example.example_output.code,
                precond_aux=example.example_input.precond_aux,
                precond=example.example_input.precond,
                postcond_aux=example.example_input.postcond_aux,
                postcond=example.example_input.postcond,
            ),
            example_output=GenProofOutput(
                imports=example.example_output.imports,
                proof_aux=example.example_output.proof_aux,
                proof=example.example_output.proof,
            ),
        )
        for example in examples
    ]


def transform_specproof_to_spec_fewshot_examples(
    examples: List[FewshotExample[GenSpecProofInput, GenSpecProofOutput]],
) -> List[FewshotExample[GenSpecInput, GenSpecOutput]]:
    return [
        FewshotExample(
            example_input=GenSpecInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=merge_imports(
                    [
                        example.example_input.task_imports,
                        example.example_input.code_imports,
                    ]
                ),
                task_aux=example.example_input.task_aux,
                precond_desc=example.example_input.precond_desc,
                postcond_desc=example.example_input.postcond_desc,
                ref_code_aux=example.example_input.code_aux,
                ref_code=example.example_input.code,
            ),
            example_output=GenSpecOutput(
                imports=example.example_output.imports,
                precond_aux=example.example_output.precond_aux,
                precond=example.example_output.precond,
                postcond_aux=example.example_output.postcond_aux,
                postcond=example.example_output.postcond,
            ),
        )
        for example in examples
    ]


def transform_specproof_to_proof_fewshot_examples(
    examples: List[FewshotExample[GenSpecProofInput, GenSpecProofOutput]],
) -> List[FewshotExample[GenProofInput, GenProofOutput]]:
    return [
        FewshotExample(
            example_input=GenProofInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=merge_imports(
                    [
                        example.example_input.task_imports,
                        example.example_input.code_imports,
                    ]
                ),
                task_aux=example.example_input.task_aux,
                code_spec_imports=example.example_output.imports,
                code_aux=example.example_output.precond_aux,
                code=example.example_output.precond,
                precond_aux=example.example_output.precond_aux,
                precond=example.example_output.precond,
                postcond_aux=example.example_output.postcond_aux,
                postcond=example.example_output.postcond,
            ),
            example_output=GenProofOutput(
                imports=example.example_output.imports,
                proof_aux=example.example_output.proof_aux,
                proof=example.example_output.proof,
            ),
        )
        for example in examples
    ]


def transform_codespecproof_to_codespec_fewshot_examples(
    examples: List[FewshotExample[GenCodeSpecProofInput, GenCodeSpecProofOutput]],
) -> List[FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]]:
    return [
        FewshotExample(
            example_input=example.example_input,
            example_output=GenCodeSpecOutput(
                imports=example.example_output.imports,
                code_aux=example.example_output.code_aux,
                code=example.example_output.code,
                precond_aux=example.example_output.precond_aux,
                precond=example.example_output.precond,
                postcond_aux=example.example_output.postcond_aux,
                postcond=example.example_output.postcond,
            ),
        )
        for example in examples
    ]


# TODO: we are using some example output to construct the input, double check
# but it should be ok, we probably don't need examples for proofgen anyways
def transform_codespecproof_to_proof_fewshot_examples(
    examples: List[FewshotExample[GenCodeSpecProofInput, GenCodeSpecProofOutput]],
) -> List[FewshotExample[GenProofInput, GenProofOutput]]:
    return [
        FewshotExample(
            example_input=GenProofInput(
                description=example.example_input.description,
                signature=example.example_input.signature,
                task_imports=example.example_input.task_imports,
                task_aux=example.example_input.task_aux,
                code_spec_imports=example.example_output.imports,
                code_aux=example.example_output.code_aux,
                code=example.example_output.code,
                precond_aux=example.example_output.precond_aux,
                precond=example.example_output.precond,
                postcond_aux=example.example_output.postcond_aux,
                postcond=example.example_output.postcond,
            ),
            example_output=GenProofOutput(
                imports="",
                proof_aux=example.example_output.proof_aux,
                proof=example.example_output.proof,
            ),
        )
        for example in examples
    ]


class SimpleSolution(Solution):
    class Preference(Enum):
        NO_GENERATED_AS_REF = 0
        USE_GENERATED_CODE_AS_REF = 1
        USE_GENERATED_SPEC_AS_REF = 2

    def __init__(self, pref: Preference):
        self.pref = pref

    async def gen_code_spec(
        self,
        data_id: str,
        input: GenCodeSpecInput,
        fewshot_examples: List[FewshotExample[GenCodeSpecInput, GenCodeSpecOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeSpecOutput:
        add_ref_spec_to_example = (
            self.pref == SimpleSolution.Preference.USE_GENERATED_SPEC_AS_REF
        )
        add_ref_code_to_example = (
            self.pref == SimpleSolution.Preference.USE_GENERATED_CODE_AS_REF
        )
        code_fewshot_examples = transform_codespec_to_code_fewshot_examples(
            fewshot_examples, add_ref_spec_to_example
        )
        spec_fewshot_examples = transform_codespec_to_spec_fewshot_examples(
            fewshot_examples, add_ref_code_to_example
        )
        code_input = GenCodeInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            ref_precond_aux=None,
            ref_precond=None,
            ref_postcond_aux=None,
            ref_postcond=None,
        )
        spec_input = GenSpecInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            precond_desc=input.precond_desc,
            postcond_desc=input.postcond_desc,
            ref_code_aux=None,
            ref_code=None,
        )
        match self.pref:
            case SimpleSolution.Preference.NO_GENERATED_AS_REF:
                code_output = await self.gen_code(
                    data_id, code_input, code_fewshot_examples, checkpoint
                )
                spec_output = await self.gen_spec(
                    data_id, spec_input, spec_fewshot_examples, checkpoint
                )
            case SimpleSolution.Preference.USE_GENERATED_CODE_AS_REF:
                code_output = await self.gen_code(
                    data_id, code_input, code_fewshot_examples, checkpoint
                )
                spec_input.ref_code_aux = code_output.code_aux
                spec_input.ref_code = code_output.code
                spec_output = await self.gen_spec(
                    data_id, spec_input, spec_fewshot_examples, checkpoint
                )
            case SimpleSolution.Preference.USE_GENERATED_SPEC_AS_REF:
                spec_output = await self.gen_spec(
                    data_id, spec_input, spec_fewshot_examples, checkpoint
                )
                code_input.ref_precond_aux = spec_output.precond_aux
                code_input.ref_precond = spec_output.precond
                code_input.ref_postcond_aux = spec_output.postcond_aux
                code_input.ref_postcond = spec_output.postcond
                code_output = await self.gen_code(
                    data_id, code_input, code_fewshot_examples, checkpoint
                )
        code_spec_output = GenCodeSpecOutput(
            imports=merge_imports([code_output.imports, spec_output.imports]),
            code_aux=code_output.code_aux,
            code=code_output.code,
            precond_aux=spec_output.precond_aux,
            precond=spec_output.precond,
            postcond_aux=spec_output.postcond_aux,
            postcond=spec_output.postcond,
        )
        return code_spec_output

    async def gen_code_proof(
        self,
        data_id: str,
        input: GenCodeProofInput,
        fewshot_examples: List[FewshotExample[GenCodeProofInput, GenCodeProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeProofOutput:
        code_fewshot_examples = transform_codeproof_to_code_fewshot_examples(
            fewshot_examples
        )
        proof_fewshot_examples = transform_codeproof_to_proof_fewshot_examples(
            fewshot_examples
        )

        code_input = GenCodeInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            ref_precond_aux=input.precond_aux,
            ref_precond=input.precond,
            ref_postcond_aux=input.postcond_aux,
            ref_postcond=input.postcond,
        )
        code_output = await self.gen_code(
            data_id, code_input, code_fewshot_examples, checkpoint
        )

        proof_input = GenProofInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            code_spec_imports=merge_imports([code_output.imports, input.spec_imports]),
            code_aux=code_output.code_aux,
            code=code_output.code,
            precond_aux=input.precond_aux,
            precond=input.precond,
            postcond_aux=input.postcond_aux,
            postcond=input.postcond,
        )
        proof_output = await self.gen_proof(
            data_id, proof_input, proof_fewshot_examples, checkpoint
        )

        return GenCodeProofOutput(
            imports=merge_imports([code_output.imports, proof_output.imports]),
            code_aux=code_output.code_aux,
            code=code_output.code,
            proof_aux=proof_output.proof_aux,
            proof=proof_output.proof,
        )

    async def gen_spec_proof(
        self,
        data_id: str,
        input: GenSpecProofInput,
        fewshot_examples: List[FewshotExample[GenSpecProofInput, GenSpecProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenSpecProofOutput:
        spec_fewshot_examples = transform_specproof_to_spec_fewshot_examples(
            fewshot_examples
        )
        proof_fewshot_examples = transform_specproof_to_proof_fewshot_examples(
            fewshot_examples
        )

        spec_input = GenSpecInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            precond_desc=input.precond_desc,
            postcond_desc=input.postcond_desc,
            ref_code_aux=input.code_aux,
            ref_code=input.code,
        )
        spec_output = await self.gen_spec(
            data_id, spec_input, spec_fewshot_examples, checkpoint
        )

        proof_input = GenProofInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            code_spec_imports=merge_imports([input.code_imports, spec_output.imports]),
            code_aux=spec_output.precond_aux,
            code=spec_output.precond,
            precond_aux=spec_output.precond_aux,
            precond=spec_output.precond,
            postcond_aux=spec_output.postcond_aux,
            postcond=spec_output.postcond,
        )
        proof_output = await self.gen_proof(
            data_id, proof_input, proof_fewshot_examples, checkpoint
        )

        return GenSpecProofOutput(
            imports=merge_imports([spec_output.imports, proof_output.imports]),
            precond_aux=spec_output.precond_aux,
            precond=spec_output.precond,
            postcond_aux=spec_output.postcond_aux,
            postcond=spec_output.postcond,
            proof_aux=proof_output.proof_aux,
            proof=proof_output.proof,
        )

    async def gen_code_spec_proof(
        self,
        data_id: str,
        input: GenCodeSpecProofInput,
        fewshot_examples: List[
            FewshotExample[GenCodeSpecProofInput, GenCodeSpecProofOutput]
        ],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenCodeSpecProofOutput:
        code_spec_fewshot_examples = (
            transform_codespecproof_to_codespec_fewshot_examples(fewshot_examples)
        )
        proof_fewshot_examples = transform_codespecproof_to_proof_fewshot_examples(
            fewshot_examples
        )

        code_spec_output = await self.gen_code_spec(
            data_id, input, code_spec_fewshot_examples, checkpoint
        )
        proof_input = GenProofInput(
            description=input.description,
            signature=input.signature,
            task_imports=input.task_imports,
            task_aux=input.task_aux,
            code_spec_imports=code_spec_output.imports,
            code_aux=code_spec_output.code_aux,
            code=code_spec_output.code,
            precond_aux=code_spec_output.precond_aux,
            precond=code_spec_output.precond,
            postcond_aux=code_spec_output.postcond_aux,
            postcond=code_spec_output.postcond,
        )
        proof_output = await self.gen_proof(
            data_id, proof_input, proof_fewshot_examples, checkpoint
        )

        return GenCodeSpecProofOutput(
            imports=merge_imports([code_spec_output.imports, proof_output.imports]),
            code_aux=code_spec_output.code_aux,
            code=code_spec_output.code,
            precond_aux=code_spec_output.precond_aux,
            precond=code_spec_output.precond,
            postcond_aux=code_spec_output.postcond_aux,
            postcond=code_spec_output.postcond,
            proof_aux=proof_output.proof_aux,
            proof=proof_output.proof,
        )
