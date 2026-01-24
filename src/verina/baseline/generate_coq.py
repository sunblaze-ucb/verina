"""Coq-specific DSPy signatures and generation functions for baseline.

This module provides Coq-specific prompts and generation functions,
mirroring the Lean baseline in generate.py but adapted for Coq syntax.
"""

import json
import os
from datetime import datetime
from pathlib import Path
from typing import List, Type

from dspy import (
    InputField,
    Module,
    OutputField,
)
from dspy import (
    Signature as DspySignature,
)

from verina.utils.logging import logger

# Directory to store LLM raw responses for debugging
LLM_RESPONSE_LOG_DIR = os.environ.get("LLM_RESPONSE_LOG_DIR", "")


def log_llm_response(task_type: str, task_template: str, response: any, output: any) -> None:
    """Log raw LLM response for debugging.

    Args:
        task_type: Type of task (code, spec, proof)
        task_template: The input template sent to LLM
        response: Raw DSPy response object
        output: Cleaned output object
    """
    if not LLM_RESPONSE_LOG_DIR:
        return

    log_dir = Path(LLM_RESPONSE_LOG_DIR)
    log_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    log_file = log_dir / f"coq_{task_type}_{timestamp}.json"

    log_data = {
        "timestamp": timestamp,
        "task_type": task_type,
        "task_template": task_template,
        "raw_response": {k: str(v) for k, v in response.toDict().items()} if hasattr(response, 'toDict') else str(response),
        "cleaned_output": output.__dict__ if hasattr(output, '__dict__') else str(output),
    }

    try:
        with open(log_file, "w") as f:
            json.dump(log_data, f, indent=2)
        logger.debug(f"Logged LLM response to {log_file}")
    except Exception as e:
        logger.warning(f"Failed to log LLM response: {e}")


from verina.benchmark.solution import (
    FewshotExample,
    GenCodeInput,
    GenCodeOutput,
    GenProofInput,
    GenProofOutput,
    GenSpecInput,
    GenSpecOutput,
)
from verina.coq.template import CoqGenerationTaskTemplate


def create_placeholder(name: str) -> str:
    return "{{" + f"`{name}` WILL BE FILLED HERE" + "}}"


def clean_coq_output(output: str, *, isImportsOrAux: bool) -> str:
    """Clean LLM output for Coq code.

    Handles:
    - Stripping ```coq ... ``` code block markers
    - Removing "Definition" prefix for code output
    - Removing "Proof." prefix for proof output
    """
    if output is None:
        return ""

    output_lines = output.splitlines()
    try:
        # Strip code block markers
        if output_lines[0].strip().startswith("```"):
            output_lines = output_lines[1:]
        if output_lines and output_lines[-1].strip().startswith("```"):
            output_lines = output_lines[:-1]
        if len(output_lines) == 0:
            return ""

        if not isImportsOrAux:
            # Handle Definition prefix for code
            if output_lines[0].strip().startswith("Definition"):
                # Find := and take everything after
                full_output = "\n".join(output_lines)
                if ":=" in full_output:
                    output = full_output.split(":=", 1)[1].strip()
                    # Remove trailing period if present
                    if output.endswith("."):
                        output = output[:-1]
                    output_lines = output.splitlines()
            # Handle Proof. prefix for proofs
            elif output_lines[0].strip().startswith("Proof"):
                output_lines[0] = output_lines[0].replace("Proof.", "").replace("Proof", "").strip()
                if not output_lines[0]:
                    output_lines = output_lines[1:]
            # Handle Qed. suffix
            full_output = "\n".join(output_lines)
            if full_output.strip().endswith("Qed."):
                full_output = full_output.strip()[:-4].strip()
                output_lines = full_output.splitlines()

    except Exception:
        pass
    return "\n".join(output_lines)


# =============================================================================
# Coq Code Generation
# =============================================================================

COQ_GEN_CODE_PROMPT = """
You are an expert in Coq programming and theorem proving.
Please generate a Coq program that finishes the task described in `task_description` using the template provided in `task_template`.
The `task_template` is a Coq code snippet that contains placeholders (wrapped with {{}}) for the code to be generated.
The program should:
- Be well-documented with comments if necessary
- Follow Coq best practices and use appropriate Coq syntax and features
- Use Fixpoint for recursive functions with decreasing arguments
- Use match expressions for pattern matching
CRITICAL RULES:
- DO NOT add extra imports - the template already has all necessary imports
- DO NOT define any _precond or _postcond definitions - they are defined elsewhere and will cause redefinition errors
- ONLY fill in the placeholders (code_aux, code)
- code_aux should ONLY contain helper functions for the algorithm, NOT precond/postcond definitions
- The code function does NOT take a h_precond parameter - preconditions are now bool-based
Hint:
- Use Z for integers (from ZArith), nat for natural numbers
- Use list for lists, option for optional values
- Use Z.eqb for integer equality, Nat.eqb for nat equality
- For recursive functions, use Fixpoint with a decreasing argument
- IMPORTANT: Z_scope is always open, so bare number literals are interpreted as Z.
  When using nat literals, wrap them with %nat suffix (e.g., 0%nat, 1%nat, (n - 1)%nat).
  For nat arithmetic, use (a + b)%nat, (a * b)%nat, (a - b)%nat.
  For nat comparisons, use (x <=? y)%nat or (x <? y)%nat with the %nat scope.
  In match patterns on nat: use `| O =>` NOT `| 0 =>` (O is the nat zero constructor, 0 is Z).
""".strip()


class CoqBaselineGenCodeSig(DspySignature):
    task_description = InputField(desc="")
    task_template = InputField()
    imports = OutputField(
        desc="Additional Coq imports needed for `code`. Keep it empty if not needed."
    )
    code_aux = OutputField(
        desc="Auxiliary definitions for `code` (e.g., helper functions). Keep it empty if not needed."
    )
    code = OutputField(
        desc="Generated Coq code following the template signature and completing the task."
    )


CoqBaselineGenCodeSig.instructions = COQ_GEN_CODE_PROMPT


def coq_code_task_template_from_input(input: GenCodeInput) -> str:
    """Render the task template for code generation."""
    template_engine = CoqGenerationTaskTemplate(input.signature)
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
        rendered += template_engine.render_aux(input.ref_postcond_aux, "postcond") + "\n"
    if input.ref_postcond and input.ref_postcond.strip() != "":
        rendered += template_engine.render_postcond(input.ref_postcond) + "\n"
    rendered += (
        template_engine.render_aux(create_placeholder("code_aux"), "code") + "\n"
    )
    rendered += template_engine.render_code(create_placeholder("code")) + "\n"

    return f"```coq\n{rendered}```"


async def dspy_generate_coq_code(
    dspy_module: Type[Module],
    input: GenCodeInput,
    fewshot_examples: List[FewshotExample[GenCodeInput, GenCodeOutput]],
) -> GenCodeOutput:
    """Generate Coq code using DSPy."""
    generator = dspy_module(CoqBaselineGenCodeSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": coq_code_task_template_from_input(example.example_input),
            "imports": example.example_output.imports,
            "code_aux": example.example_output.code_aux,
            "code": example.example_output.code,
        }
        demos.append(demo)
    task_template = coq_code_task_template_from_input(input)
    response = await generator.acall(
        task_description=input.description,
        task_template=task_template,
        demos=demos,
    )
    output = GenCodeOutput(
        imports=clean_coq_output(response.imports, isImportsOrAux=True),
        code_aux=clean_coq_output(response.code_aux, isImportsOrAux=True),
        code=clean_coq_output(response.code, isImportsOrAux=False),
    )
    log_llm_response("code", task_template, response, output)
    return output


# =============================================================================
# Coq Specification Generation
# =============================================================================

COQ_GEN_SPEC_PROMPT = """
You are an expert in Coq programming and theorem proving.
Please generate a Coq specification that constrains the program implementation using the template provided in `task_template`.
The `task_template` is a Coq code snippet that contains placeholders (wrapped with {{}}) for the spec to be generated.
The precondition should be as permissive as possible, and the postcondition should model a sound and complete relationship between input and output of the program based on the `task_description`.

CRITICAL - Both precond and postcond MUST return bool (not Prop):
The generated specification should:
- Express BOTH preconditions AND postconditions as bool types (NOT Prop)
- Use boolean operators: && (and), || (or), negb (not)
- Use decidable comparisons: =? (Z.eqb), <=? (Z.leb), <? (Z.ltb), >=? (Z.geb), >? (Z.gtb)
- Only use `precond_aux` or `postcond_aux` when you cannot express the precondition or postcondition in the main body

Boolean operators (MUST use these, NOT Prop operators):
- Use && instead of /\\ (Prop and)
- Use || instead of \\/ (Prop or)
- Use negb instead of ~ (Prop not)
- Use forallb/existsb instead of forall/exists (for lists)
- Use =? instead of = for equality checks
- Use <=?, <?, >=?, >? instead of <=, <, >=, >

Example precond patterns (bool):
- Good: true                                      (* no constraints *)
- Good: (n >=? 0)%Z                              (* Z bool comparison *)
- Good: (length lst >=? 1)%nat                   (* nat bool comparison *)
- Good: negb (length lst =? 0)%nat               (* non-empty list *)
- Bad:  n >= 0                                   (* Prop comparison - WRONG *)
- Bad:  True                                     (* Prop True - use 'true' *)
- Bad:  forall x, In x lst -> x > 0             (* Prop quantifier - WRONG *)

Example postcond patterns (bool):
- Good: (result >=? 0)%Z && (result <=? bound)%Z    (* result in valid range *)
- Good: forallb (fun x => (x <=? result)%Z) lst     (* result >= all elements *)
- Good: existsb (fun x => (x =? result)%Z) lst      (* result is in the list *)
- Good: (length result_list =? length input_list)%nat (* preserves length *)
- Bad:  (result =? x + 1)%Z                         (* just restates the algorithm - WRONG *)
- Bad:  result = expected                           (* Prop equality - WRONG *)

CRITICAL - Spec is NOT another program:
- DO NOT restate the algorithm in the spec (e.g., "result =? x + 1" for increment)
- DO check meaningful properties (e.g., "result >? x" for increment)
- The spec should describe WHAT the result should satisfy, not HOW to compute it
- Think: "What properties must a correct result have?" not "What is the formula?"

IMPORTANT:
- DO NOT add extra imports - the template already has all necessary imports
- DO NOT redefine any existing definitions in the template
- ONLY fill in the placeholders (precond_aux, precond, postcond_aux, postcond)
- Keep precond_aux and postcond_aux empty unless absolutely necessary
- The default precondition is 'true' (lowercase bool) if there are no constraints
- IMPORTANT: Z_scope is always open, so bare number literals are interpreted as Z.
  When using nat literals, wrap them with %nat suffix (e.g., 0%nat, 1%nat, (length lst)%nat).
  For nat arithmetic in specs, use (a + b)%nat, (a * b)%nat, (a - b)%nat.
  For nat bool comparisons, use (x <=? y)%nat or (x <? y)%nat with the %nat scope.
  In match patterns on nat: use `| O =>` NOT `| 0 =>` (O is the nat zero constructor, 0 is Z).
""".strip()


class CoqBaselineGenSpecSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    precond_desc = InputField(
        desc="Natural language description of the precondition. If empty, derive from task description."
    )
    postcond_desc = InputField(
        desc="Natural language description of the postcondition. If empty, derive from task description."
    )
    imports = OutputField(
        desc="Additional Coq imports needed for `precond` and `postcond`. Keep it empty if not needed."
    )
    precond_aux = OutputField(
        desc="Auxiliary definitions for `precond`. Keep it empty if not needed."
    )
    precond = OutputField(desc="Generated Coq code specifying the precondition as a bool. Use 'true' for no constraints, boolean operators (&&, ||, negb), and decidable comparisons (=?, <=?, <?, >=?, >?).")
    postcond_aux = OutputField(
        desc="Auxiliary definitions for `postcond`. Keep it empty if not needed."
    )
    postcond = OutputField(desc="Generated Coq code specifying the postcondition as a bool. Use boolean operators (&&, ||, negb, forallb, existsb) and decidable comparisons. Check PROPERTIES, not algorithm restatement.")


CoqBaselineGenSpecSig.instructions = COQ_GEN_SPEC_PROMPT


def coq_spec_task_template_from_input(input: GenSpecInput) -> str:
    """Render the task template for specification generation."""
    template_engine = CoqGenerationTaskTemplate(input.signature)
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
        template_engine.render_aux(create_placeholder("postcond_aux"), "postcond") + "\n"
    )
    rendered += template_engine.render_postcond(create_placeholder("postcond")) + "\n"

    # Include reference code if available
    if input.ref_code_aux and input.ref_code_aux.strip() != "":
        rendered += template_engine.render_aux(input.ref_code_aux, "code") + "\n"
    if input.ref_code and input.ref_code.strip() != "":
        rendered += template_engine.render_code(input.ref_code) + "\n"

    return f"```coq\n{rendered}```"


async def dspy_generate_coq_spec(
    dspy_module: Type[Module],
    input: GenSpecInput,
    fewshot_examples: List[FewshotExample[GenSpecInput, GenSpecOutput]],
) -> GenSpecOutput:
    """Generate Coq specification using DSPy."""
    generator = dspy_module(CoqBaselineGenSpecSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": coq_spec_task_template_from_input(example.example_input),
            "precond_desc": example.example_input.precond_desc,
            "postcond_desc": example.example_input.postcond_desc,
            "imports": example.example_output.imports,
            "precond_aux": example.example_output.precond_aux,
            "precond": example.example_output.precond,
            "postcond_aux": example.example_output.postcond_aux,
            "postcond": example.example_output.postcond,
        }
        demos.append(demo)
    task_template = coq_spec_task_template_from_input(input)
    response = await generator.acall(
        task_description=input.description,
        task_template=task_template,
        precond_desc=input.precond_desc,
        postcond_desc=input.postcond_desc,
        demos=demos,
    )
    output = GenSpecOutput(
        imports=clean_coq_output(response.imports, isImportsOrAux=True),
        precond_aux=clean_coq_output(response.precond_aux, isImportsOrAux=True),
        precond=clean_coq_output(response.precond, isImportsOrAux=False),
        postcond_aux=clean_coq_output(response.postcond_aux, isImportsOrAux=True),
        postcond=clean_coq_output(response.postcond, isImportsOrAux=False),
    )
    log_llm_response("spec", task_template, response, output)
    return output


# =============================================================================
# Coq Proof Generation
# =============================================================================

COQ_GEN_PROOF_PROMPT = """
You are an expert in Coq programming and theorem proving.
Please generate a Coq proof that the program satisfies the specification using the template provided in `task_template`.
The `task_template` is a Coq code snippet that contains placeholders (wrapped with {{}}) for the proof to be generated.

IMPORTANT for Bool specifications:
- The goal format is: precond params = true -> postcond params (code params) = true
- First, intro the precondition hypothesis: intro H_precond
- Then use native_compute or vm_compute to evaluate the bool expression
- Finish with reflexivity

Common proof pattern for Bool specs:
  intro H_precond.
  native_compute. reflexivity.

If native_compute doesn't work directly:
  intro H_precond.
  unfold postcond, precond. simpl.
  (* may need destruct or case analysis on booleans *)
  reflexivity.

CRITICAL - Output format:
- The template already includes "Proof." before and "Qed." after your proof
- DO NOT include "Proof." or "Qed." in your output - only the tactics
- DO NOT use Admitted, admit, or Abort - provide a complete proof
- DO NOT use axioms or assume

Example - what to output:
  intro H_precond.
  native_compute. reflexivity.

Example - what NOT to output:
  Proof.
  intro H_precond.
  native_compute. reflexivity.
  Qed.

IMPORTANT:
- DO NOT add extra imports - the template already has all necessary imports
- DO NOT redefine any existing definitions - use unfold to work with them
- ONLY fill in the placeholders (imports, proof_aux, proof)
- Keep imports and proof_aux empty unless absolutely necessary
- The proof should work with the EXACT definitions in the template
Hint:
- Use intro H_precond to introduce the precondition
- Use native_compute or vm_compute for fast bool evaluation
- Use reflexivity after computation reduces to true = true
- Use unfold to expand definitions if needed
- Use simpl for simplification
- Use destruct for case analysis on booleans
- Use lia for linear integer arithmetic (may need conversion from bool to Prop)
""".strip()


class CoqBaselineGenProofSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    imports = OutputField(
        desc="Additional Coq imports needed for `proof`. Keep it empty if not needed."
    )
    proof_aux = OutputField(
        desc="Auxiliary lemmas for `proof`. Keep it empty if not needed."
    )
    proof = OutputField(
        desc="Generated Coq proof tactics only. Do NOT include 'Proof.' or 'Qed.' - the template adds them. Do NOT use Admitted or admit."
    )


CoqBaselineGenProofSig.instructions = COQ_GEN_PROOF_PROMPT


COQ_GEN_PROOF_WITH_REFINEMENT_PROMPT = """
You are an expert in Coq programming and theorem proving.
Please generate a Coq proof that the program satisfies the specification using the template provided in `task_template`.
The `task_template` is a Coq code snippet that contains placeholders (wrapped with {{}}) for the proof to be generated.

IMPORTANT for Bool specifications:
- The goal format is: precond params = true -> postcond params (code params) = true
- First, intro the precondition hypothesis: intro H_precond
- Then use native_compute or vm_compute to evaluate the bool expression
- Finish with reflexivity

Common proof pattern for Bool specs:
  intro H_precond.
  native_compute. reflexivity.

If native_compute doesn't work directly:
  intro H_precond.
  unfold postcond, precond. simpl.
  (* may need destruct or case analysis on booleans *)
  reflexivity.

CRITICAL - Output format:
- The template already includes "Proof." before and "Qed." after your proof
- DO NOT include "Proof." or "Qed." in your output - only the tactics
- DO NOT use Admitted, admit, or Abort - provide a complete proof
- DO NOT use axioms or assume

Example - what to output:
  intro H_precond.
  native_compute. reflexivity.

Example - what NOT to output:
  Proof.
  intro H_precond.
  native_compute. reflexivity.
  Qed.

IMPORTANT:
- DO NOT add extra imports - the template already has all necessary imports
- DO NOT redefine any existing definitions - use unfold to work with them
- ONLY fill in the placeholders (imports, proof_aux, proof)
- Keep imports and proof_aux empty unless absolutely necessary
- The proof should work with the EXACT definitions in the template
Hint:
- Use intro H_precond to introduce the precondition
- Use native_compute or vm_compute for fast bool evaluation
- Use reflexivity after computation reduces to true = true
- Use unfold to expand definitions if needed
- Use simpl for simplification
- Use destruct for case analysis on booleans
- Use lia for linear integer arithmetic (may need conversion from bool to Prop)

Furthermore, `prev_error` is the error message from the previous proving attempt.
Please use the `prev_imports`, `prev_proof_aux`, and `prev_proof` as references to improve the generated proof.
- You can ignore unused variable warnings in the error message.
- Focus on fixing the actual proof errors.
""".strip()


class CoqBaselineGenProofWithRefinementSig(DspySignature):
    task_description = InputField()
    task_template = InputField()
    prev_imports = InputField(desc="Previously generated imports for reference.")
    prev_proof_aux = InputField(
        desc="Previously generated proof auxiliary for reference."
    )
    prev_proof = InputField(desc="Previously generated proof for reference.")
    prev_error = InputField(desc="Error message from the previous proving attempt.")
    imports = OutputField(
        desc="Additional Coq imports needed for `proof`. Keep it empty if not needed."
    )
    proof_aux = OutputField(
        desc="Auxiliary lemmas for `proof`. Keep it empty if not needed."
    )
    proof = OutputField(
        desc="Generated Coq proof tactics only. Do NOT include 'Proof.' or 'Qed.' - the template adds them. Do NOT use Admitted or admit."
    )


CoqBaselineGenProofWithRefinementSig.instructions = COQ_GEN_PROOF_WITH_REFINEMENT_PROMPT


def coq_proof_content_from_input_output(
    input: GenProofInput,
    output: GenProofOutput,
) -> str:
    """Render full Coq content from proof input and output."""
    template_engine = CoqGenerationTaskTemplate(input.signature)
    rendered = ""

    if input.task_imports.strip() != "":
        rendered += template_engine.render_imports(input.task_imports, "task") + "\n"
    if input.code_spec_imports.strip() != "":
        rendered += template_engine.render_imports(input.code_spec_imports, "solution") + "\n"
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


def coq_proof_task_template_from_input(input: GenProofInput) -> str:
    """Render the task template for proof generation."""
    placeholder_output = GenProofOutput(
        imports=create_placeholder("imports"),
        proof_aux=create_placeholder("proof_aux"),
        proof=create_placeholder("proof"),
    )
    rendered = coq_proof_content_from_input_output(input, placeholder_output)
    return f"```coq\n{rendered}```"


async def dspy_generate_coq_proof(
    dspy_module: Type[Module],
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    """Generate Coq proof using DSPy."""
    generator = dspy_module(CoqBaselineGenProofSig)
    demos = []
    for example in fewshot_examples:
        demo = {
            "task_description": example.example_input.description,
            "task_template": coq_proof_task_template_from_input(example.example_input),
            "imports": example.example_output.imports,
            "proof_aux": example.example_output.proof_aux,
            "proof": example.example_output.proof,
        }
        demos.append(demo)
    task_template = coq_proof_task_template_from_input(input)
    response = await generator.acall(
        task_description=input.description,
        task_template=task_template,
        demos=demos,
    )
    output = GenProofOutput(
        imports=clean_coq_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_coq_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_coq_output(response.proof, isImportsOrAux=False),
    )
    log_llm_response("proof", task_template, response, output)
    return output


async def dspy_generate_coq_proof_with_refinement(
    dspy_module: Type[Module],
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    """Generate Coq proof with refinement using DSPy."""
    generator = dspy_module(CoqBaselineGenProofWithRefinementSig)
    response = await generator.acall(
        task_description=input.description,
        task_template=coq_proof_task_template_from_input(input),
        prev_imports=prev_output.imports,
        prev_proof_aux=prev_output.proof_aux,
        prev_proof=prev_output.proof,
        prev_error=prev_error,
    )
    output = GenProofOutput(
        imports=clean_coq_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_coq_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_coq_output(response.proof, isImportsOrAux=False),
    )
    return output
