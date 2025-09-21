import asyncio
import re
from typing import List, Optional

import dspy

from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.generate import (
    clean_output,
    proof_lean_content_from_input_output,
    proof_task_template_from_input,
)
from verina.benchmark.metrics import metric_lean_compile
from verina.benchmark.report import EvaluationTaskArtifact
from verina.benchmark.solution import (
    FewshotExample,
    GenProofInput,
    GenProofOutput,
)
from verina.utils.logging import logger

max_retries = 1  # Number of retries for errors of failures to follow dspy format


DEEPSEEK_PROVER_COT_PROMPT = """
Complete the following Lean 4 code:

{}

Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()


class CustomPromptHandler:
    def __init__(self, prompt_template: Optional[str]):
        if prompt_template == "DEEPSEEK_PROVER_COT_PROMPT":
            self.prompt_template = DEEPSEEK_PROVER_COT_PROMPT
        elif prompt_template is None:
            self.prompt_template = DEEPSEEK_PROVER_COT_PROMPT
        else:
            raise ValueError(f"Unknown prompt template: {prompt_template}")

    def create_messages(self, question: str) -> list[dict[str, str]]:
        user_prompt = self.prompt_template.format(question)

        return [{"role": "user", "content": user_prompt}]

    def create_refinement_messages(
        self, messages: list[dict[str, str]], raw_response: str, compiler_feedback: str
    ) -> list[dict[str, str]]:
        messages.append({"role": "assistant", "content": raw_response})
        # From Goedel Prover v2 `DeepSeekCoTHandler`
        user_feedback_content = (
            f"The proof is not correct. Following is the compilation error message.\n\n{compiler_feedback}"
            "\n\nBefore producing the Lean 4 code to formally prove the given theorem, provide a detailed analysis of the error message."
        )
        messages.append({"role": "user", "content": user_feedback_content})
        return messages


def prepare_prompt(
    handler: CustomPromptHandler,
    input: GenProofInput,
) -> list[dict[str, str]]:
    task_template = proof_task_template_from_input(input)
    # Remove markers to avoid confusion
    lines = filter(lambda x: not x.strip().startswith("--"), task_template.split("\n"))
    messages = handler.create_messages("\n".join(lines))
    return messages


def extract_code(response: str):
    pattern = r"```lean4?\n(.*?)\n?```"
    matches = re.findall(pattern, response, re.DOTALL)
    if matches:
        return matches[-1]
    return "None"


def remove_provided_content(
    response: str, provided_content: str, remove_above_lines: int
) -> str:
    loc = response.find(provided_content)
    if loc == -1:
        return response
    above_lines = response[:loc].split("\n")
    below_lines = response[loc + len(provided_content) :].split("\n")
    if len(above_lines) <= remove_above_lines:
        return "\n".join(below_lines)
    return "\n".join(above_lines[-remove_above_lines:] + below_lines)


def remove_same_indentation_lines(lines: list[str]) -> str:
    if not lines:
        return ""
    # Find the first non-empty line to determine the indentation level
    for line in lines:
        if line.strip():  # Non-empty line
            indentation = len(line) - len(line.lstrip())
            break
    else:
        return ""  # All lines are empty

    # Remove lines with the same indentation level until a different indentation level is found, and then stop
    start_idx = 0
    for line in lines:
        if len(line) - len(line.lstrip()) >= indentation:
            # Special handling for top-level definitions (indentation == 0)
            if indentation == 0:
                # Stop if two consecutive empty lines are found
                if (
                    line.strip() == ""
                    and start_idx != 0
                    and lines[start_idx - 1].strip() == ""
                ):
                    break
            start_idx += 1
        else:
            break
    return "\n".join(lines[start_idx:])


def remove_def(response: str, def_name: str) -> str:
    # Best effort to remove the provided def from the response
    lines = response.splitlines()
    # Find the last line that starts with "def {def_name}" and get its index directly
    def_index = -1
    for i in reversed(range(len(lines))):
        if lines[i].lstrip().startswith(f"def {def_name}"):
            def_index = i
            break
    if def_index == -1:
        return response
    # Remove lines with the same indentation level until a different indentation level is found, and then stop
    remaining_lines = (
        lines[:def_index]
        + remove_same_indentation_lines(lines[def_index + 1 :]).splitlines()
    )
    return "\n".join(remaining_lines)


def remove_code_spec(response, input: GenProofInput) -> str:
    # Best effort to remove the provided code/spec from the response
    response = remove_provided_content(response, input.code_aux, 0)
    response = remove_provided_content(response, input.precond_aux, 0)
    response = remove_provided_content(response, input.postcond_aux, 0)
    response = remove_provided_content(response, input.code, 1)
    response = remove_provided_content(response, input.precond, 2)
    response = remove_provided_content(response, input.postcond, 2)

    response = remove_def(response, input.signature.name)
    response = remove_def(response, f"{input.signature.name}_precond")
    response = remove_def(response, f"{input.signature.name}_postcond")

    response = response.replace("@[reducible, simp]\n\n", "\n").strip()
    if response == "@[reducible, simp]":
        # Handle special case where only the attribute is left
        response = ""

    return response


def parse_model_response(input: GenProofInput, response: str) -> GenProofOutput:
    lean_code = extract_code(response)
    theorem_name = f"{input.signature.name}_postcond_satisfied"
    theorem_pattern = r"theorem\s+" + re.escape(theorem_name) + r"\s+.*?\s+:= by"
    theorem_match = re.search(theorem_pattern, lean_code, re.DOTALL)
    if not theorem_match:
        return GenProofOutput(
            imports="",
            proof_aux="",
            proof="sorry",
        )
    span = theorem_match.span()
    imports_and_aux = lean_code[: span[0]].strip().splitlines()
    imports = "\n".join(line for line in imports_and_aux if line.startswith("import "))
    proof_aux = "\n".join(
        line for line in imports_and_aux if not line.startswith("import ")
    )
    proof_aux = remove_code_spec(proof_aux, input)
    if "import Mathlib" not in imports:
        imports = "import Mathlib\n" + imports
    if "import Aesop" not in imports:
        imports = "import Aesop\n" + imports
    proof = lean_code[span[1] :]
    return GenProofOutput(
        imports=clean_output(imports, isImportsOrAux=True),
        proof_aux=clean_output(proof_aux, isImportsOrAux=True),
        proof=clean_output(proof, isImportsOrAux=False),
    )


async def direct_lm_generate(lm: dspy.LM, messages: list[dict[str, str]]) -> str:
    output = await lm.acall(messages=messages)
    return output[0]  # type: ignore


class CustomPromptProofBaselineSolution(BaselineSolution):
    def __init__(self, config: BaselineConfig):
        super().__init__(config)

        self.prompt_handler = CustomPromptHandler(config.custom_prompt_template)

    def get_lm(self) -> dspy.LM:
        return dspy.settings.lm

    @staticmethod
    def name() -> str:
        return "custom_prompt_baseline"

    async def gen_proof(
        self,
        data_id: str,
        input: GenProofInput,
        fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenProofOutput:
        # TODO: currently we don't use fewshot examples in custom prompt
        if self.config.resume_from_checkpoint and checkpoint is not None:
            if checkpoint.proof != "":
                logger.info(f"Use proof result from checkpoint for data_id {data_id}")
                return GenProofOutput(
                    imports=checkpoint.imports,
                    proof_aux=checkpoint.proof_aux,
                    proof=checkpoint.proof,
                )
        logger.info(f"CustomPromptBaseline: Generating proof for data_id {data_id}")
        retry_count = 0
        while retry_count < max_retries:
            try:
                prompt = prepare_prompt(self.prompt_handler, input)
                lm = self.get_lm()
                response = await direct_lm_generate(lm, prompt)
                output = parse_model_response(input, response)
                return output
            except Exception as e:
                logger.error(f"Error generating proof for data_id {data_id}: {e}")
                retry_count += 1
                await asyncio.sleep(1)
        return GenProofOutput(
            imports="",
            proof_aux="",
            proof="",
        )


class CustomPromptProofRefinementBaselineSolution(CustomPromptProofBaselineSolution):
    @staticmethod
    def name() -> str:
        return "custom_prompt_proof_refinement_baseline"

    async def gen_proof(
        self,
        data_id: str,
        input: GenProofInput,
        fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
        checkpoint: Optional[EvaluationTaskArtifact] = None,
    ) -> GenProofOutput:
        # We don't use checkpoint for proof refinement
        # TODO: figure out checkpoint
        lm = self.get_lm()
        try:
            prompt = prepare_prompt(self.prompt_handler, input)
            response = await direct_lm_generate(lm, prompt)
            output = parse_model_response(input, response)
        except Exception as e:
            logger.error(f"Error during proof generation: {e}")
            response = ""
            output = GenProofOutput(
                imports="",
                proof_aux="",
                proof="",
            )

        if self.config.refinements is None:
            return output

        refined_times = 0
        while refined_times < self.config.refinements:
            refined_times += 1
            logger.info(
                f"Refining proof for data_id {data_id} for the {refined_times} time"
            )

            # Check if the proof is correct
            if output.proof != "":
                cheat_codes = ["sorry", "admit", "axiom"]
                if any(code in output.proof for code in cheat_codes) or any(
                    code in output.proof_aux for code in cheat_codes
                ):
                    can_compile = False
                    error_message = "Proof contains cheat codes."
                else:
                    lean_content = proof_lean_content_from_input_output(input, output)
                    can_compile, error_message = await metric_lean_compile(lean_content)
            else:
                can_compile = False
                error_message = "Failed to generate proof. The model response does not follow the expected format."
            if can_compile:
                output.extra_info["refined_times"] = refined_times
                return output
            try:
                prompt = prepare_prompt(self.prompt_handler, input)
                prompt = self.prompt_handler.create_refinement_messages(
                    messages=prompt,
                    raw_response=response,
                    compiler_feedback=error_message,
                )
                response = await direct_lm_generate(lm, prompt)
                output = parse_model_response(input, response)
            except Exception as e:
                logger.error(f"Error during proof refinement: {e}")
        return output
