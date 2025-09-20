from typing import List

from dspy import LM

from verina.baseline.generate import (
    clean_output,
    proof_lean_content_from_input_output,
    proof_task_template_from_input,
)
from verina.benchmark.solution import (
    FewshotExample,
    GenProofInput,
    GenProofOutput,
)


def initial_parse(output: str) -> str:
    # Make sure lean program is generated
    if "```lean" not in output:
        raise ValueError("There's not ```lean code block in the final output")
    # Extract lean program from the llm output
    text = output.split("```lean")[-1]
    if text[0] == "4":
        text = text[1:]
    if "```" not in text:
        raise ValueError("```lean4 and ``` delimeters not in pair")
    text = text.split("```")[0].strip()
    return text


# dsprover generates a single string for output, consisting of detailed thoughts and final lean program
# the name of the theorem is provided to distinguish between "proof" and "proof_aux"
def parsing_output(output: str, thm: str) -> GenProofOutput:
    # Initial parsing the output by extracting the final lean program, ommitting the rest details
    output = initial_parse(output)
    if f"theorem {thm}" not in output:
        raise ValueError(f'theorem "{thm}" is not proven in the output')
    # Distinguishing between imports, proof_aux, and proof in the lean program generated
    proof_aux = ""
    proof = ""
    imports = ""
    # dsprover normally won't generate imports. Therefore, we include the two most commonly used libraries in "imports" field.
    if "import Mathlib" not in output:
        imports = imports + "import Mathlib\n"
    if "import Aesop" not in output:
        imports = imports + "import Aesop\n"
    # Reading line by line and splitting them into corresponding output fields
    pf = False
    pfaux = False
    waiting = ""
    for line in output.splitlines():
        # skip the empty line
        if line.strip() == "":
            continue
        elif line.strip().startwith("--"):
            waiting = waiting + line.strip()+ "\n"
            continue
        # if the name of the theorem appear, then this line and the following lines should be the proof
        if thm in line and "theorem" in line and "_satisfied" in line:
            pf = True
            pfaux = False
            proof = proof + "\n" + waiting + line + "\n"
            waiting = ""
        # for the rest theorems or defs, they are proof_aux
        elif "theorem" in line or "def" in line:
            pfaux = True
            pf = False
            proof_aux = proof_aux + "\n" + waiting + line + "\n"
            waiting = ""
        # import only takes one line (for each library)
        elif "import" in line:
            imports = imports + line + "\n"
            pf = False
            pfaux = False
            waiting = ""
        elif pf:
            proof = proof + waiting + line + "\n"
        elif pfaux:
            proof_aux = proof_aux + waiting + line + "\n"
        # lines can be decorators to a theorem/def. They should go with what comes next
        elif "@[" in line:
            waiting = waiting + line + "\n"
        else:
            raise ValueError(
                f"Can not identify what output field this line belongs to: {line}"
            )
    return GenProofOutput(
        imports=imports.strip(),
        proof_aux=proof_aux.strip(),
        proof=proof.strip(),
    )


async def dsprover2_generate_proof(
    lm: LM,
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    task_template = proof_task_template_from_input(input)
    messages = []
    prompt = """
    Complete the following Lean 4 code:

    {}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    for example in fewshot_examples:
        i = proof_task_template_from_input(example.example_input)
        o = proof_lean_content_from_input_output(
            example.example_input, example.example_output
        )
        messages.append({"role": "user", "content": prompt.format(i) + "\n\n" + o})
    content = prompt.format(task_template)
    messages.append({"role": "user", "content": content})
    output = await lm.acall(messages=messages)
    response = parsing_output(
        output=output[0], thm=input.signature.name
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output


async def dsprover2_generate_proof_with_refinement(
    lm: LM,
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    task_template = proof_task_template_from_input(input)
    prev_code = proof_lean_content_from_input_output(input, prev_output)
    prompt = f"""
    Complete the following Lean 4 code:

    {task_template}

    Given the following pseudo solution

    {prev_code}

    with the error: 

    {prev_error}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    messages = [{"role": "user", "content": prompt}]
    output = await lm.acall(messages=messages)
    response = parsing_output(
        output=output[0], thm=input.signature.name + "_postcond_satisfied"
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output
