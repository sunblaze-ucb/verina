from typing import List, Type

from dspy import (
    ChatAdapter,
    InputField,
    Module,
    OutputField,
)
from dspy import (
    Signature as DspySignature,
)
import dspy
from rich import print

from verina.benchmark.solution import (
    FewshotExample,
    GenCodeInput,
    GenCodeOutput,
    GenProofInput,
    GenProofOutput,
    GenSpecInput,
    GenSpecOutput,
)
from verina.dataset.schema import Parameter, Signature
from verina.dataset.template import LeanGenerationTaskTemplate


def create_placeholder(name: str) -> str:
    return "{{" + f"`{name}` WILL BE FILLED HERE" + "}}"


def clean_output(output: str, *, isImportsOrAux: bool) -> str:
    if output is None:
        return ""

    output_lines = output.splitlines()
    try:
        if output_lines[0].strip().startswith("```"):
            output_lines = output_lines[1:]
        if output_lines[-1].strip().startswith("```"):
            output_lines = output_lines[:-1]
        if len(output_lines) == 0:
            return ""
        if not isImportsOrAux:
            if output_lines[0].strip().startswith("by"):
                output_lines[0] = output_lines[0].split("by", 1)[1].strip()
            if output_lines[0].strip().startswith("def"):
                output_lines[0] = output_lines[0].split(":=", 1)[1].strip()
            if output_lines[0].strip().startswith("theorem"):
                output = "by".join("\n".join(output_lines).split("by")[1:])
                output_lines = output.splitlines()

    except Exception:
        pass
    return "\n".join(output_lines)


GEN_CODE_PROMPT = """
You are an expert in Lean 4 programming and theorem proving.
Please generate a Lean 4 program that finishes the task described in `task_description` using the template provided in `task_template`.
The `task_template` is a Lean 4 code snippet that contains placeholders (warpped with {{}}) for the code to be generated.
The program should:
- Be well-documented with comments if necessary
- Follow Lean 4 best practices and use appropriate Lean 4 syntax and features
- DO NOT use Lean 3 syntax or features
- DO NOT import Std or Init
Hint:
- Use a[i]! instead of a[i] when a is an array or a list when necessary
""".strip()


class BaselineGenCodeSig(DspySignature):
    task_description = InputField(desc="")
    task_template = InputField()
    imports = OutputField(
        desc="Imports needed for `code`. Keep it empty if not needed."
    )
    code_aux = OutputField(
        desc="Auxiliary definitions for `code`. Keep it empty if not needed."
    )
    code = OutputField(
        desc="Generated Lean 4 code following the template signature and complete the task."
    )


BaselineGenCodeSig.instructions = GEN_CODE_PROMPT


def code_task_template_from_input(input: GenCodeInput) -> str:
    template_engine = LeanGenerationTaskTemplate(input.signature)
    rendered = ""
    if input.task_imports.strip() != "":
        rendered += template_engine.render_imports(input.task_imports, "task") + "\n"
    rendered += (
        template_engine.render_imports(create_placeholder("imports"), "solution") + "\n"
    )
    if input.task_aux.strip() != "":
        rendered += template_engine.render_aux(input.task_aux, "task") + "\n"
    if input.ref_precond_aux and input.ref_precond_aux.strip() != "":
        rendered += template_engine.render_aux(input.ref_precond_aux, "precond") + "\n"
    if input.ref_precond and input.ref_precond.strip() != "":
        rendered += template_engine.render_precond(input.ref_precond) + "\n"
    if input.ref_postcond_aux and input.ref_postcond_aux.strip() != "":
        rendered += (
            template_engine.render_aux(input.ref_postcond_aux, "postcond") + "\n"
        )
    if input.ref_postcond and input.ref_postcond.strip() != "":
        rendered += template_engine.render_postcond(input.ref_postcond) + "\n"
    rendered += (
        template_engine.render_aux(create_placeholder("code_aux"), "code") + "\n"
    )
    rendered += template_engine.render_code(create_placeholder("code")) + "\n"

    return f"```lean4\n{rendered}```"


async def dspy_generate_code(
    dspy_module: Type[Module],
    input: GenCodeInput,
    fewshot_examples: List[FewshotExample[GenCodeInput, GenCodeOutput]],
) -> GenCodeOutput:
    generator = dspy_module(BaselineGenCodeSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": code_task_template_from_input(example.example_input),
            "imports": example.example_output.imports,
            "code_aux": example.example_output.code_aux,
            "code": example.example_output.code,
        }
        demos.append(demo)
    response = await generator.acall(
        task_description=input.description,
        task_template=code_task_template_from_input(input),
        demos=demos,
    )
    output = GenCodeOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        code_aux=clean_output(response.code_aux, isImportsOrAux=True),
        code=clean_output(response.code, isImportsOrAux=False),
    )
    return output


GEN_SPEC_PROMPT = """
You are an expert in Lean 4 programming and theorem proving.
Please generate a Lean 4 specification that constrains the program implementation using the template provided in `task_template`.
The `task_template` is a Lean 4 code snippet that contains placeholders (warpped with {{}}) for the spec to be generated.
The precondition should be as permissive as possible, and the postcondition should model a sound an complete relationship between input and output of the program based on the `task_description`.
The generated specification should:
- Be well-documented with comments if necessary
- Follow Lean 4 best practices and use appropriate Lean 4 syntax and features
- DO NOT use Lean 3 syntax or features
- DO NOT import Std or Init
- Only use `precond_aux` or `postcond_aux` when you cannot express the precondition or postcondition in the main body of the specification
- add @[reducible, simp] attribute to the definitions in `precond_aux` or `postcond_aux`
Hint:
- Use a[i]! instead of a[i] when a is an array or a list when necessary
""".strip()


class BaselineGenSpecSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    precond_desc = InputField(
        desc="Natural language description of the precondition. If empty, you should instead derive from the task description."
    )
    postcond_desc = InputField(
        desc="Natural language description of the postcondition. If empty, you should instead derive from the task description."
    )
    imports = OutputField(
        desc="Imports needed for `precond` and `postcond`. Keep it empty if not needed."
    )
    precond_aux = OutputField(
        desc="Auxiliary definitions for `precond`. Keep it empty if not needed."
    )
    precond = OutputField(desc="Generated Lean 4 code specifying the precondition.")
    postcond_aux = OutputField(
        desc="Auxiliary definitions for `postcond`. Keep it empty if not needed."
    )
    postcond = OutputField(desc="Generated Lean 4 code specifying the postcondition.")


BaselineGenSpecSig.instructions = GEN_SPEC_PROMPT


def spec_task_template_from_input(input: GenSpecInput) -> str:
    template_engine = LeanGenerationTaskTemplate(input.signature)
    rendered = ""
    if input.task_imports.strip() != "":
        rendered += template_engine.render_imports(input.task_imports, "task") + "\n"
    rendered += (
        template_engine.render_imports(create_placeholder("imports"), "solution") + "\n"
    )
    if input.task_aux.strip() != "":
        rendered += template_engine.render_aux(input.task_aux, "task") + "\n"
    rendered += (
        template_engine.render_aux(create_placeholder("precond_aux"), "precond") + "\n"
    )
    rendered += template_engine.render_precond(create_placeholder("precond")) + "\n"
    rendered += (
        template_engine.render_aux(create_placeholder("postcond_aux"), "postcond")
        + "\n"
    )
    rendered += template_engine.render_postcond(create_placeholder("postcond")) + "\n"
    if input.ref_code_aux and input.ref_code_aux.strip() != "":
        rendered += template_engine.render_aux(input.ref_code_aux, "code") + "\n"
    if input.ref_code and input.ref_code.strip() != "":
        rendered += template_engine.render_code(input.ref_code) + "\n"

    return f"```lean4\n{rendered}```"


async def dspy_generate_spec(
    dspy_module: Type[Module],
    input: GenSpecInput,
    fewshot_examples: List[FewshotExample[GenSpecInput, GenSpecOutput]],
) -> GenSpecOutput:
    generator = dspy_module(BaselineGenSpecSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": spec_task_template_from_input(example.example_input),
            "precond_desc": example.example_input.precond_desc,
            "postcond_desc": example.example_input.postcond_desc,
            "imports": example.example_output.imports,
            "precond_aux": example.example_output.precond_aux,
            "precond": example.example_output.precond,
            "postcond_aux": example.example_output.postcond_aux,
            "postcond": example.example_output.postcond,
        }
        demos.append(demo)
    response = await generator.acall(
        task_description=input.description,
        task_template=spec_task_template_from_input(input),
        precond_desc=input.precond_desc,
        postcond_desc=input.postcond_desc,
        demos=demos,
    )
    output = GenSpecOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        precond_aux=clean_output(response.precond_aux, isImportsOrAux=True),
        precond=clean_output(response.precond, isImportsOrAux=False),
        postcond_aux=clean_output(response.postcond_aux, isImportsOrAux=True),
        postcond=clean_output(response.postcond, isImportsOrAux=False),
    )
    return output


GEN_PROOF_PROMPT = """
You are an expert in Lean 4 programming and theorem proving.
Please generate a Lean 4 proof that the program satisfies the specification using the template provided in `task_template`.
The `task_template` is a Lean 4 code snippet that contains placeholders (warpped with {{}}) for the proof to be generated.
The proof should:
- Be well-documented with comments if necessary
- Follow Lean 4 best practices and use appropriate Lean 4 syntax and features
- DO NOT use Lean 3 syntax or features
- DO NOT import Std or Init
- DO NOT use cheat codes like `sorry`
Hint:
- Unfold the implementation and specification definitions when necessary
- Unfold the precondition definitions at h_precond when necessary
""".strip()


class BaselineGenProofSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    imports = OutputField(
        desc="Imports needed for `proof`. Keep it empty if not needed."
    )
    proof_aux = OutputField(
        desc="Auxiliary definitions and lemma for `proof`. Keep it empty if not needed."
    )
    proof = OutputField(
        desc="Generated Lean 4 proof that the program satisfies the specification."
    )


BaselineGenProofSig.instructions = GEN_PROOF_PROMPT


GEN_PROOF_WITH_REFINEMENT_PROMPT = """
You are an expert in Lean 4 programming and theorem proving.
Please generate a Lean 4 proof that the program satisfies the specification using the template provided in `task_template`.
The `task_template` is a Lean 4 code snippet that contains placeholders (warpped with {{}}) for the proof to be generated.
The proof should:
- Be well-documented with comments if necessary
- Follow Lean 4 best practices and use appropriate Lean 4 syntax and features
- DO NOT use Lean 3 syntax or features
- DO NOT import Std or Init
- DO NOT use cheat codes like `sorry`
Hint:
- Unfold the implementation and specification definitions when necessary
- Unfold the precondition definitions at h_precond when necessary

Furthermore, `prev_error` is the error message from the previous proving attempt.
Please use the `prev_imports`, `prev_proof_aux`, and `prev_proof` as references to improve the generated proof.
- You can ignore unused variable warnings in the error message.
""".strip()


class BaselineGenProofWithRefinementSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    prev_imports = InputField(desc="Previously generated imports for reference.")
    prev_proof_aux = InputField(
        desc="Previously generated proof auxiliary for reference."
    )
    prev_proof = InputField(desc="Previously generated proof for reference.")
    prev_error = InputField(desc="Error message from the previous proving attempt.")
    imports = OutputField(
        desc="Imports needed for `proof`. Keep it empty if not needed."
    )
    proof_aux = OutputField(
        desc="Auxiliary definitions and lemma for `proof`. Keep it empty if not needed."
    )
    proof = OutputField(
        desc="Generated Lean 4 proof that the program satisfies the specification."
    )


BaselineGenProofWithRefinementSig.instructions = GEN_PROOF_WITH_REFINEMENT_PROMPT


def proof_lean_content_from_input_output(
    input: GenProofInput,
    output: GenProofOutput,
) -> str:
    template_engine = LeanGenerationTaskTemplate(input.signature)
    rendered = ""
    if input.task_imports.strip() != "":
        rendered += template_engine.render_imports(input.task_imports, "task") + "\n"
    if input.code_spec_imports.strip() != "":
        rendered += (
            template_engine.render_imports(input.code_spec_imports, "solution") + "\n"
        )
    rendered += template_engine.render_imports(output.imports, "proof") + "\n"
    if input.task_aux.strip() != "":
        rendered += template_engine.render_aux(input.task_aux, "task") + "\n"
    if input.precond_aux.strip() != "":
        rendered += template_engine.render_aux(input.precond_aux, "precond") + "\n"
    rendered += template_engine.render_precond(input.precond) + "\n"
    if input.code_aux.strip() != "":
        rendered += template_engine.render_aux(input.code_aux, "code") + "\n"
    rendered += template_engine.render_code(input.code) + "\n"
    if input.postcond_aux.strip() != "":
        rendered += template_engine.render_aux(input.postcond_aux, "postcond") + "\n"
    rendered += template_engine.render_postcond(input.postcond) + "\n"
    rendered += template_engine.render_aux(output.proof_aux, "proof") + "\n"
    rendered += template_engine.render_proof(output.proof) + "\n"
    return rendered


def proof_task_template_from_input(input: GenProofInput) -> str:
    placeholder_output = GenProofOutput(
        imports=create_placeholder("imports"),
        proof_aux=create_placeholder("proof_aux"),
        proof=create_placeholder("proof"),
    )
    rendered = proof_lean_content_from_input_output(input, placeholder_output)
    return f"```lean4\n{rendered}```"

# litellm specific proof generation

def initial_parse(output: str) -> str:
    lastline = output.strip().splitlines()[-1]
    if "```lean4" not in output:
        raise ValueError("There's not ```lean4 code block in the final output")
    text=output.split("```lean4")[-1]
    if "```" not in text:
        raise ValueError("```lean4 and ``` delimeters not in pair")
    text=text.split("```")[0].strip()
    return text

def parsing_output(output: str, thm: str) -> GenProofOutput:
    output=initial_parse(output)
    if f"theorem {thm}" not in output:
        raise ValueError(f"theorem \"{thm}\" is not proven in the output")
    proof_aux=""
    proof=""
    imports=""
    if "import Mathlib" not in output:
        imports=imports+"import Mathlib\n"
    if "import Aesop" not in output:
        imports=imports+"import Aesop\n"
    pf=False
    pfaux=False
    waiting=""
    for line in output.splitlines():
        if line.strip()=="":
            continue
        if thm in line:
            pf=True
            pfaux=False
            proof=proof+"\n"+waiting+line+"\n"
            waiting=""
        elif "theorem" in line or "def" in line:
            pfaux=True
            pf=False
            proof_aux=proof_aux+"\n"+waiting+line+"\n"
            waiting=""
        elif "import" in line:
            imports=imports+line+"\n"
            pf=False
            pfaux=False
            waiting=""
        elif pf:
            proof=proof+waiting+line+"\n"
        elif pfaux:
            proof_aux=proof_aux+waiting+line+"\n"
        elif "@[" in line:
            waiting=waiting+line+"\n"
        else:
            raise ValueError(f"Can not identify what output field does this belong to: {line}")
    return GenProofOutput(imports=imports.strip(),
        proof_aux=proof_aux.strip(),
        proof=proof.strip(),
    )

async def no_example_litellm_generate_proof(
    dspy_module: Type[Module],
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    task_template=proof_task_template_from_input(input)
    prompt = """
    Complete the following Lean 4 code:

    {}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    content=prompt.format(task_template)
    messages=[{"role":"user", "content":content}]
    generator=dspy.settings.lm
    output=await generator.acall(messages=messages)
    response = parsing_output(output=output[0], thm=input.signature.name+"_postcond_satisfied")
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output

async def litellm_generate_proof(
    dspy_module: Type[Module],
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    task_template=proof_task_template_from_input(input)
    messages=[]
    prompt = """
    Complete the following Lean 4 code:

    {}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    for example in fewshot_examples:
        i=proof_task_template_from_input(example.example_input)
        o=proof_lean_content_from_input_output(example.example_input,example.example_output)
        messages.append({"role":"user", "content":prompt.format(i)+"\n\n"+o})
    content=prompt.format(task_template)
    messages.append({"role":"user", "content":content})
    generator=dspy.settings.lm
    output=await generator.acall(messages=messages)
    response = parsing_output(output=output[0], thm=input.signature.name+"_postcond_satisfied")
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output

async def litellm_generate_proof_with_refinement(
    dspy_module: Type[Module],
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    generator=dspy.settings.lm
    task_template=proof_task_template_from_input(input)
    prev_code=proof_lean_content_from_input_output(input, prev_output)
    prompt = f"""
    Complete the following Lean 4 code:

    {task_template}

    Given the following pseudo solution

    {prev_code}

    with the error: 

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    messages=[{"role":"user", "content":prompt}]
    output=await generator.acall(messages=messages)
    response = parsing_output(output=output[0], thm=input.signature.name+"_postcond_satisfied")
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output

async def dspy_generate_proof_with_refinement(
    dspy_module: Type[Module],
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    generator = dspy_module(BaselineGenProofWithRefinementSig)
    response = await generator.acall(
        task_description=input.description,
        task_template=proof_task_template_from_input(input),
        prev_imports=prev_output.imports,
        prev_proof_aux=prev_output.proof_aux,
        prev_proof=prev_output.proof,
        prev_error=prev_error,
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output

async def dspy_generate_proof(
    dspy_module: Type[Module],
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    generator = dspy_module(BaselineGenProofSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": proof_task_template_from_input(example.example_input),
            "imports": example.example_output.imports,
            "proof_aux": example.example_output.proof_aux,
            "proof": example.example_output.proof,
        }
        demos.append(demo)
    response = await generator.acall(
        task_description=input.description,
        task_template=proof_task_template_from_input(input),
        demos=demos,
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output


# Do not support fewshot examples for refinement
async def dspy_generate_proof_with_refinement(
    dspy_module: Type[Module],
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    generator = dspy_module(BaselineGenProofWithRefinementSig)
    response = await generator.acall(
        task_description=input.description,
        task_template=proof_task_template_from_input(input),
        prev_imports=prev_output.imports,
        prev_proof_aux=prev_output.proof_aux,
        prev_proof=prev_output.proof,
        prev_error=prev_error,
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output


if __name__ == "__main__":
    codeInputExample1 = GenCodeInput(
        description="Generate a function that adds two numbers",
        task_imports="-- import task",
        task_aux="def task_aux : Prop := True",
        signature=Signature(
            name="add",
            parameters=[
                Parameter(param_name="x", param_type="Int"),
                Parameter(param_name="y", param_type="Int"),
            ],
            return_type="Int",
        ),
        ref_precond_aux="def precond_aux : Prop := True",
        ref_precond="True -- precond",
        ref_postcond_aux="def postcond_aux : Prop := True",
        ref_postcond="True -- postcond",
    )
    codeOutputExample1 = GenCodeOutput(
        imports="-- import code",
        code_aux="def code_aux : Prop := True",
        code="x + y",
    )
    codeInput = GenCodeInput(
        description="Generate a function that substracts two numbers",
        signature=Signature(
            name="add",
            parameters=[
                Parameter(param_name="x", param_type="Int"),
                Parameter(param_name="y", param_type="Int"),
            ],
            return_type="Int",
        ),
        task_imports="-- import task",
        task_aux="def task_aux : Prop := True",
        ref_precond_aux="def precond_aux : Prop := True",
        ref_precond="True -- precond",
        ref_postcond_aux="def postcond_aux : Prop := True",
        ref_postcond="True -- postcond",
    )

    demos = [
        {
            "task_description": codeInputExample1.description,
            "task_template": code_task_template_from_input(codeInputExample1),
            "imports": codeOutputExample1.imports,
            "code_aux": codeOutputExample1.code_aux,
            "code": codeOutputExample1.code,
        }
    ]

    adapter = ChatAdapter()
    msgs = adapter.format(
        BaselineGenCodeSig,
        demos=demos,
        inputs={
            "task_description": codeInput.description,
            "task_template": code_task_template_from_input(codeInput),
        },
    )
    for msg in msgs:
        print("role:", msg["role"])
        print("content:\n", msg["content"])
