#!/usr/bin/env python3
"""Translate Lean tests to Coq test format with type-checking validation.

This script:
1. Finds all task directories with test.json but no coq_test.json
2. Uses LLM to convert test values to Coq literal format
3. Validates by type-checking in the context of task.v
4. Refines with LLM on type errors
5. Saves validated tests to coq_test.json

Usage:
    uv run python scripts/translate_tests_to_coq.py
    uv run python scripts/translate_tests_to_coq.py --dry-run
    uv run python scripts/translate_tests_to_coq.py --filter verina_basic_1,verina_basic_2
"""

import asyncio
import json
import logging
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import typer
from dotenv import load_dotenv
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from verina.dataset.schema import Signature, Parameter, TestCase
from verina.utils.lm import LMConfig

load_dotenv(override=True)

# Setup logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

console = Console()

# Project root
ROOT_DIR = Path(__file__).parent.parent
DATASETS_DIR = ROOT_DIR / "datasets" / "verina"


class DockerContainerManager:
    """Manages a long-running Coq Docker container for efficient compilation."""

    def __init__(
        self,
        image: str = "verina-coq",
        container_name: str = "verina-coq-test-translator",
    ):
        self.image = image
        self.container_name = container_name
        self.container_id: Optional[str] = None

    async def start(self) -> str:
        """Start a long-running container, return container ID."""
        await self._run_docker(["rm", "-f", self.container_name], ignore_errors=True)

        proc = await asyncio.create_subprocess_exec(
            "docker", "run", "-d",
            "--name", self.container_name,
            "-v", f"{ROOT_DIR}:/workspace",
            "-w", "/workspace",
            self.image,
            "tail", "-f", "/dev/null",
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await proc.communicate()

        if proc.returncode != 0:
            raise RuntimeError(f"Failed to start container: {stderr.decode()}")

        self.container_id = stdout.decode().strip()[:12]
        logger.info(f"Started container {self.container_name} ({self.container_id})")
        return self.container_id

    async def exec_coqc(self, file_path: Path, timeout: int = 60) -> Tuple[bool, str]:
        """Execute coqc inside the running container."""
        relative_path = file_path.relative_to(ROOT_DIR)
        cmd = [
            "docker", "exec", self.container_name,
            "bash", "-lc", f"coqc /workspace/{relative_path}",
        ]

        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout,
            )
            output = stdout.decode() + stderr.decode()
            return proc.returncode == 0, output
        except asyncio.TimeoutError:
            return False, f"Compilation timed out after {timeout}s"

    async def stop(self):
        """Stop and remove the container."""
        if self.container_id:
            await self._run_docker(["rm", "-f", self.container_name], ignore_errors=True)
            logger.info(f"Stopped container {self.container_name}")
            self.container_id = None

    async def _run_docker(self, args: list, ignore_errors: bool = False) -> Tuple[int, str]:
        """Run a docker command."""
        proc = await asyncio.create_subprocess_exec(
            "docker", *args,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await proc.communicate()
        if not ignore_errors and proc.returncode != 0:
            raise RuntimeError(f"Docker command failed: {stderr.decode()}")
        return proc.returncode, stdout.decode() + stderr.decode()

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, *args):
        await self.stop()


# LLM prompt for batch test conversion (all tests in one call)
TEST_CONVERSION_PROMPT = """Convert ALL the following test cases from JSON/Lean format to Coq literal format.

## Coq Function Signature:
```coq
{signature}
```

## Parameter Types:
{param_types}

## Return Type: {return_type}

## Test Cases (JSON array):
```json
{test_cases}
```

## Conversion Rules:
For TYPE "Z" (integers): 5 -> "(5)%Z", -3 -> "(-3)%Z", list: [1,2] -> "[(1)%Z; (2)%Z]"
For TYPE "nat" (natural numbers): 5 -> "5", list: [1,2] -> "[1; 2]"  (NO %Z!)
For TYPE "bool": true -> "true", false -> "false"
For TYPE "string": "hi" -> "\"hi\"%string"
For TYPE "option X": null/None -> "None", value -> "Some <converted_value>"
For TYPE "list X": use semicolons [a; b; c], apply type X rules to elements

CRITICAL: Match types exactly! Use nat syntax for nat, Z syntax for Z.

Output a JSON array with ALL converted test cases:
```json
[
  {{"input": {{...}}, "expected": "...", "unexpected": ["..."]}},
  ...
]
```"""


# LLM prompt for reject inputs conversion (input only, no expected/unexpected)
REJECT_INPUTS_CONVERSION_PROMPT = """Convert ALL the following reject inputs from JSON/Lean format to Coq literal format.

## Coq Function Signature:
```coq
{signature}
```

## Parameter Types:
{param_types}

## Reject Inputs (JSON array) - these are inputs that should fail the precondition:
```json
{reject_inputs}
```

## Conversion Rules:
For TYPE "Z" (integers): 5 -> "(5)%Z", -3 -> "(-3)%Z", list: [1,2] -> "[(1)%Z; (2)%Z]"
For TYPE "nat" (natural numbers): 5 -> "5", list: [1,2] -> "[1; 2]"  (NO %Z!)
For TYPE "bool": true -> "true", false -> "false"
For TYPE "string": "hi" -> "\"hi\"%string"
For TYPE "option X": null/None -> "None", value -> "Some <converted_value>"
For TYPE "list X": use semicolons [a; b; c], apply type X rules to elements

CRITICAL: Match types exactly! Use nat syntax for nat, Z syntax for Z.

Output a JSON array with ALL converted reject inputs:
```json
[
  {{"input": {{...}}}},
  ...
]
```"""


REFINEMENT_PROMPT = """The following Coq test case has type errors. Fix the literal values.

## Coq Function Signature:
```coq
{signature}
```

## Current Test Case:
```json
{test_case}
```

## Type Check Error:
{error}

## Instructions:
Fix the Coq literal values to match the expected types. Common fixes:
- Missing %Z suffix for integers: 5 -> "(5)%Z"
- Wrong list syntax: [1, 2] -> "[(1)%Z; (2)%Z]"
- Wrong boolean: True -> "true"
- Missing parentheses for negative numbers: -3 -> "(-3)%Z"

Output ONLY the corrected JSON object."""


class TestTranslator:
    """Translates test cases to Coq format using LLM."""

    def __init__(self, lm_config: Optional[LMConfig] = None):
        self.lm_config = lm_config
        self._lm = None

    @property
    def lm(self):
        """Lazy-load the LLM."""
        if self._lm is None and self.lm_config:
            import dspy
            self._lm = self.lm_config.get_model()
            dspy.configure(lm=self._lm)
        return self._lm

    def get_signature_string(self, task_v_content: str) -> str:
        """Extract the function signature from task.v content."""
        # Extract the Definition line for the main function
        lines = task_v_content.split('\n')
        signature_lines = []
        in_def = False
        for line in lines:
            if line.strip().startswith('Definition') and '_precond' not in line and '_postcond' not in line:
                in_def = True
            if in_def:
                signature_lines.append(line)
                if ':=' in line:
                    break
        return '\n'.join(signature_lines)

    async def convert_all_tests(
        self,
        test_cases: List[Dict[str, Any]],
        signature: str,
        coq_sig: Optional[Signature] = None,
    ) -> List[Dict[str, Any]]:
        """Convert all test cases to Coq format in a single LLM call."""
        if not self.lm:
            # Fallback to simple conversion without LLM
            return [self._simple_convert(tc, coq_sig) for tc in test_cases]

        # Extract parameter types for the prompt
        param_types = ""
        return_type = "unknown"
        if coq_sig:
            for p in coq_sig.parameters:
                param_types += f"- {p.param_name}: {p.param_type}\n"
            return_type = coq_sig.return_type

        prompt = TEST_CONVERSION_PROMPT.format(
            signature=signature,
            param_types=param_types.strip() or "See signature above",
            return_type=return_type,
            test_cases=json.dumps(test_cases, indent=2),
        )

        response = self.lm(prompt)
        if response and len(response) > 0:
            result = self._parse_json_array_response(response[0], test_cases)
            if len(result) == len(test_cases):
                return result
        # Fallback to simple conversion
        return [self._simple_convert(tc, coq_sig) for tc in test_cases]

    async def convert_all_reject_inputs(
        self,
        reject_inputs: List[Dict[str, Any]],
        signature: str,
        coq_sig: Optional[Signature] = None,
    ) -> List[Dict[str, Any]]:
        """Convert all reject inputs to Coq format in a single LLM call."""
        if not reject_inputs:
            return []

        if not self.lm:
            # Fallback to simple conversion without LLM
            return [self._simple_convert_reject(ri, coq_sig) for ri in reject_inputs]

        # Extract parameter types for the prompt
        param_types = ""
        if coq_sig:
            for p in coq_sig.parameters:
                param_types += f"- {p.param_name}: {p.param_type}\n"

        prompt = REJECT_INPUTS_CONVERSION_PROMPT.format(
            signature=signature,
            param_types=param_types.strip() or "See signature above",
            reject_inputs=json.dumps(reject_inputs, indent=2),
        )

        response = self.lm(prompt)
        if response and len(response) > 0:
            result = self._parse_json_array_response(response[0], reject_inputs)
            if len(result) == len(reject_inputs):
                return result
        # Fallback to simple conversion
        return [self._simple_convert_reject(ri, coq_sig) for ri in reject_inputs]

    def _simple_convert_reject(self, reject_input: Dict[str, Any], coq_sig: Optional[Signature] = None) -> Dict[str, Any]:
        """Simple conversion for reject inputs (input only, no expected/unexpected)."""
        # Build type map from signature
        param_types = {}
        if coq_sig:
            for p in coq_sig.parameters:
                param_types[p.param_name] = p.param_type

        def convert_value(val: Any, coq_type: str = "Z") -> str:
            coq_type_lower = coq_type.lower()

            if isinstance(val, bool):
                return "true" if val else "false"
            elif isinstance(val, int):
                # Check if nat or Z
                if "nat" in coq_type_lower:
                    return str(val)
                else:  # Z or unknown
                    return f"({val})%Z"
            elif isinstance(val, str):
                return f'"{val}"%string'
            elif isinstance(val, list):
                # Determine element type
                elem_type = "Z"
                if "list" in coq_type_lower:
                    elem_type = coq_type_lower.replace("(", "").replace(")", "").replace("list", "").strip()
                    if not elem_type:
                        elem_type = "Z"
                items = [convert_value(v, elem_type) for v in val]
                return "[" + "; ".join(items) + "]"
            elif val is None:
                return "None"
            else:
                return str(val)

        result = {"input": {}}
        for key, val in reject_input.get("input", {}).items():
            ptype = param_types.get(key, "Z")
            result["input"][key] = convert_value(val, ptype)

        return result

    def _parse_json_array_response(self, response: str, fallback: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Parse JSON array from LLM response."""
        response = response.strip()

        # Remove markdown code blocks if present
        if '```json' in response:
            match = re.search(r'```json\s*(.*?)```', response, re.DOTALL)
            if match:
                response = match.group(1).strip()
        elif '```' in response:
            match = re.search(r'```\s*(.*?)```', response, re.DOTALL)
            if match:
                response = match.group(1).strip()

        try:
            result = json.loads(response)
            if isinstance(result, list):
                return result
        except json.JSONDecodeError:
            logger.warning(f"Failed to parse JSON array response: {response[:300]}")
        return fallback

    async def refine_test_case(
        self,
        test_case: Dict[str, Any],
        signature: str,
        error: str,
    ) -> Dict[str, Any]:
        """Refine a test case that failed type checking."""
        if not self.lm:
            return test_case

        prompt = REFINEMENT_PROMPT.format(
            signature=signature,
            test_case=json.dumps(test_case, indent=2),
            error=error[:1500],
        )

        response = self.lm(prompt)
        if response and len(response) > 0:
            return self._parse_json_response(response[0], test_case)
        return test_case

    def _parse_json_response(self, response: str, fallback: Dict[str, Any]) -> Dict[str, Any]:
        """Parse JSON from LLM response."""
        # Try to extract JSON from response
        response = response.strip()

        # Remove markdown code blocks if present
        if '```json' in response:
            match = re.search(r'```json\s*(.*?)```', response, re.DOTALL)
            if match:
                response = match.group(1).strip()
        elif '```' in response:
            match = re.search(r'```\s*(.*?)```', response, re.DOTALL)
            if match:
                response = match.group(1).strip()

        try:
            return json.loads(response)
        except json.JSONDecodeError:
            logger.warning(f"Failed to parse JSON response: {response[:200]}")
            return fallback

    def _simple_convert(self, test_case: Dict[str, Any], coq_sig: Optional[Signature] = None) -> Dict[str, Any]:
        """Simple conversion without LLM - type-aware conversion."""
        # Build type map from signature
        param_types = {}
        return_type = "Z"  # default
        if coq_sig:
            for p in coq_sig.parameters:
                param_types[p.param_name] = p.param_type
            return_type = coq_sig.return_type

        def convert_value(val: Any, coq_type: str = "Z") -> str:
            coq_type_lower = coq_type.lower()

            if isinstance(val, bool):
                return "true" if val else "false"
            elif isinstance(val, int):
                # Check if nat or Z
                if "nat" in coq_type_lower:
                    return str(val)
                else:  # Z or unknown
                    return f"({val})%Z"
            elif isinstance(val, str):
                return f'"{val}"%string'
            elif isinstance(val, list):
                # Determine element type
                elem_type = "Z"
                if "list" in coq_type_lower:
                    # Extract element type from "list X" or "(list X)"
                    elem_type = coq_type_lower.replace("(", "").replace(")", "").replace("list", "").strip()
                    if not elem_type:
                        elem_type = "Z"
                items = [convert_value(v, elem_type) for v in val]
                return "[" + "; ".join(items) + "]"
            elif val is None:
                return "None"
            else:
                return str(val)

        def convert_option_value(val: Any, coq_type: str) -> str:
            """Handle option types."""
            if val is None:
                return "None"
            # Extract inner type from "option X"
            inner_type = coq_type.lower().replace("(", "").replace(")", "").replace("option", "").strip()
            if not inner_type:
                inner_type = "Z"
            return f"Some {convert_value(val, inner_type)}"

        result = {"input": {}, "expected": None, "unexpected": []}

        for key, val in test_case.get("input", {}).items():
            ptype = param_types.get(key, "Z")
            result["input"][key] = convert_value(val, ptype)

        # Handle return type (might be option)
        expected_val = test_case.get("expected")
        if "option" in return_type.lower():
            result["expected"] = convert_option_value(expected_val, return_type)
            result["unexpected"] = [convert_option_value(v, return_type) for v in test_case.get("unexpected", [])]
        else:
            result["expected"] = convert_value(expected_val, return_type)
            result["unexpected"] = [convert_value(v, return_type) for v in test_case.get("unexpected", [])]

        return result


class TestValidator:
    """Validates Coq test cases by type checking."""

    def __init__(self, container: DockerContainerManager):
        self.container = container

    def generate_type_check_code(
        self,
        task_v_content: str,
        coq_sig: Signature,
        test_case: Dict[str, Any],
        test_idx: int,
    ) -> str:
        """Generate Coq code to type-check a test case.

        For type-checking purposes, we only verify that:
        1. Each input value has the correct parameter type
        2. The expected value has the correct return type
        3. The unexpected values have the correct return type

        We do NOT call the function (which would require satisfying the precondition).
        """
        check_code = f"\n(* Type check test case {test_idx} *)\n"

        # Check each input parameter type
        for param in coq_sig.parameters:
            val = test_case["input"].get(param.param_name, "")
            check_code += f"Definition _test_{test_idx}_input_{param.param_name}_check : {param.param_type} := {val}.\n"

        # Check expected value type
        expected = test_case.get("expected", "")
        check_code += f"Definition _test_{test_idx}_expected_check : {coq_sig.return_type} := {expected}.\n"

        # Add unexpected value checks
        for i, unexpected in enumerate(test_case.get("unexpected", [])):
            check_code += f"Definition _test_{test_idx}_unexpected_{i}_check : {coq_sig.return_type} := {unexpected}.\n"

        return check_code

    async def validate_tests(
        self,
        task_dir: Path,
        task_v_content: str,
        coq_sig: Signature,
        coq_tests: List[Dict[str, Any]],
    ) -> Tuple[bool, str, List[int]]:
        """Validate all test cases by type checking.

        Returns: (success, error_message, failed_indices)
        """
        # Generate validation code - include task.v content which has imports
        validation_code = task_v_content + "\n\n(* Test case type checks *)\n"

        # Add ZArith import if any test uses %Z notation
        all_tests_str = json.dumps(coq_tests)
        if "%Z" in all_tests_str:
            validation_code = "Require Import ZArith.\nOpen Scope Z_scope.\n\n" + validation_code

        for idx, test_case in enumerate(coq_tests):
            validation_code += self.generate_type_check_code(
                task_v_content, coq_sig, test_case, idx
            )

        # Write and compile
        check_file = task_dir / "_test_check.v"
        check_file.write_text(validation_code)

        try:
            success, output = await self.container.exec_coqc(check_file)

            if success:
                return True, "", []

            # Parse which tests failed
            failed_indices = self._parse_failed_tests(output, len(coq_tests))
            return False, output, failed_indices
        finally:
            # Clean up
            check_file.unlink(missing_ok=True)
            # Also clean up .vo/.glob files
            for ext in [".vo", ".glob", ".vok", ".vos"]:
                (task_dir / f"_test_check{ext}").unlink(missing_ok=True)

    def _parse_failed_tests(self, error_output: str, num_tests: int) -> List[int]:
        """Parse which test indices failed from error output."""
        failed = []
        for idx in range(num_tests):
            if f"_test_{idx}_" in error_output:
                failed.append(idx)
        # If can't determine, mark all as potentially failed
        if not failed:
            failed = list(range(num_tests))
        return failed

    def generate_reject_input_type_check_code(
        self,
        task_v_content: str,
        coq_sig: Signature,
        reject_input: Dict[str, Any],
        idx: int,
    ) -> str:
        """Generate Coq code to type-check a reject input."""
        check_code = f"\n(* Type check reject input {idx} *)\n"

        # Check each input parameter type
        for param in coq_sig.parameters:
            val = reject_input["input"].get(param.param_name, "")
            check_code += f"Definition _reject_{idx}_input_{param.param_name}_check : {param.param_type} := {val}.\n"

        return check_code

    async def validate_reject_inputs(
        self,
        task_dir: Path,
        task_v_content: str,
        coq_sig: Signature,
        coq_reject_inputs: List[Dict[str, Any]],
    ) -> Tuple[bool, str, List[int]]:
        """Validate all reject inputs by type checking.

        Returns: (success, error_message, failed_indices)
        """
        if not coq_reject_inputs:
            return True, "", []

        # Generate validation code
        validation_code = task_v_content + "\n\n(* Reject input type checks *)\n"

        # Add ZArith import if any input uses %Z notation
        all_inputs_str = json.dumps(coq_reject_inputs)
        if "%Z" in all_inputs_str:
            validation_code = "Require Import ZArith.\nOpen Scope Z_scope.\n\n" + validation_code

        for idx, reject_input in enumerate(coq_reject_inputs):
            validation_code += self.generate_reject_input_type_check_code(
                task_v_content, coq_sig, reject_input, idx
            )

        # Write and compile
        check_file = task_dir / "_reject_check.v"
        check_file.write_text(validation_code)

        try:
            success, output = await self.container.exec_coqc(check_file)

            if success:
                return True, "", []

            # Parse which inputs failed
            failed_indices = []
            for idx in range(len(coq_reject_inputs)):
                if f"_reject_{idx}_" in output:
                    failed_indices.append(idx)
            if not failed_indices:
                failed_indices = list(range(len(coq_reject_inputs)))

            return False, output, failed_indices
        finally:
            # Clean up
            check_file.unlink(missing_ok=True)
            for ext in [".vo", ".glob", ".vok", ".vos"]:
                (task_dir / f"_reject_check{ext}").unlink(missing_ok=True)


async def process_single_task(
    task_dir: Path,
    translator: TestTranslator,
    validator: TestValidator,
    semaphore: asyncio.Semaphore,
    max_retries: int = 3,
    force: bool = False,
) -> dict:
    """Process a single task directory."""
    async with semaphore:
        task_json_path = task_dir / "task.json"
        task_v_path = task_dir / "task.v"
        test_json_path = task_dir / "test.json"
        coq_test_path = task_dir / "coq_test.json"

        # Skip if coq_test.json already exists (unless force)
        if coq_test_path.exists() and not force:
            return {"task_id": task_dir.name, "status": "skipped", "reason": "exists"}

        # Check required files exist
        if not task_v_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_v"}
        if not test_json_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_test_json"}
        if not task_json_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_json"}

        try:
            # Load files
            task_json = json.loads(task_json_path.read_text())
            task_v_content = task_v_path.read_text()
            lean_tests = json.loads(test_json_path.read_text())

            # Get Coq signature
            if "coq_signature" not in task_json:
                return {"task_id": task_dir.name, "status": "skipped", "reason": "no_coq_signature"}

            coq_sig = Signature(**task_json["coq_signature"])
            signature_str = translator.get_signature_string(task_v_content)

            # Convert all test cases in a single LLM call
            coq_tests = await translator.convert_all_tests(lean_tests, signature_str, coq_sig)

            # Validate and refine
            for attempt in range(max_retries + 1):
                success, error, failed_indices = await validator.validate_tests(
                    task_dir, task_v_content, coq_sig, coq_tests
                )

                if success:
                    # Save successful tests
                    coq_test_path.write_text(json.dumps(coq_tests, indent=4))
                    return {
                        "task_id": task_dir.name,
                        "status": "success",
                        "attempts": attempt + 1,
                        "num_tests": len(coq_tests),
                    }

                if attempt == max_retries:
                    # Max retries reached
                    logger.warning(f"Max retries for {task_dir.name}: {error[:200]}")
                    # Save failed version for inspection
                    failed_path = task_dir / "coq_test.json.failed"
                    failed_path.write_text(json.dumps({
                        "error": error[:2000],
                        "tests": coq_tests,
                    }, indent=2))
                    return {
                        "task_id": task_dir.name,
                        "status": "failed",
                        "attempts": attempt + 1,
                        "error": error[:200],
                    }

                # Refine failed tests
                logger.info(f"Refining {len(failed_indices)} tests for {task_dir.name}")
                for idx in failed_indices:
                    coq_tests[idx] = await translator.refine_test_case(
                        coq_tests[idx], signature_str, error
                    )

            return {"task_id": task_dir.name, "status": "failed", "attempts": max_retries + 1}

        except Exception as e:
            logger.error(f"Error processing {task_dir.name}: {e}")
            import traceback
            traceback.print_exc()
            return {"task_id": task_dir.name, "status": "error", "error": str(e)}


async def process_reject_inputs(
    task_dir: Path,
    translator: TestTranslator,
    validator: TestValidator,
    semaphore: asyncio.Semaphore,
    max_retries: int = 3,
    force: bool = False,
) -> dict:
    """Process reject_inputs.json for a single task directory."""
    async with semaphore:
        task_json_path = task_dir / "task.json"
        task_v_path = task_dir / "task.v"
        reject_inputs_path = task_dir / "reject_inputs.json"
        coq_reject_path = task_dir / "coq_reject_inputs.json"

        # Skip if coq_reject_inputs.json already exists (unless force)
        if coq_reject_path.exists() and not force:
            return {"task_id": task_dir.name, "status": "skipped", "reason": "exists"}

        # Check required files exist
        if not task_v_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_v"}
        if not reject_inputs_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_reject_inputs"}
        if not task_json_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_json"}

        try:
            # Load files
            task_json = json.loads(task_json_path.read_text())
            task_v_content = task_v_path.read_text()
            lean_reject_inputs = json.loads(reject_inputs_path.read_text())

            # Skip if empty
            if not lean_reject_inputs:
                # Save empty list
                coq_reject_path.write_text("[]")
                return {"task_id": task_dir.name, "status": "success", "num_inputs": 0}

            # Get Coq signature
            if "coq_signature" not in task_json:
                return {"task_id": task_dir.name, "status": "skipped", "reason": "no_coq_signature"}

            coq_sig = Signature(**task_json["coq_signature"])
            signature_str = translator.get_signature_string(task_v_content)

            # Convert all reject inputs in a single LLM call
            coq_reject_inputs = await translator.convert_all_reject_inputs(
                lean_reject_inputs, signature_str, coq_sig
            )

            # Validate and refine
            for attempt in range(max_retries + 1):
                success, error, failed_indices = await validator.validate_reject_inputs(
                    task_dir, task_v_content, coq_sig, coq_reject_inputs
                )

                if success:
                    # Save successful inputs
                    coq_reject_path.write_text(json.dumps(coq_reject_inputs, indent=4))
                    return {
                        "task_id": task_dir.name,
                        "status": "success",
                        "attempts": attempt + 1,
                        "num_inputs": len(coq_reject_inputs),
                    }

                if attempt == max_retries:
                    # Max retries reached
                    logger.warning(f"Max retries for reject inputs {task_dir.name}: {error[:200]}")
                    # Save failed version for inspection
                    failed_path = task_dir / "coq_reject_inputs.json.failed"
                    failed_path.write_text(json.dumps({
                        "error": error[:2000],
                        "inputs": coq_reject_inputs,
                    }, indent=2))
                    return {
                        "task_id": task_dir.name,
                        "status": "failed",
                        "attempts": attempt + 1,
                        "error": error[:200],
                    }

                # Refine failed inputs (reuse test case refinement)
                logger.info(f"Refining {len(failed_indices)} reject inputs for {task_dir.name}")
                for idx in failed_indices:
                    # Use refine_test_case but only for inputs
                    coq_reject_inputs[idx] = await translator.refine_test_case(
                        coq_reject_inputs[idx], signature_str, error
                    )

            return {"task_id": task_dir.name, "status": "failed", "attempts": max_retries + 1}

        except Exception as e:
            logger.error(f"Error processing reject inputs for {task_dir.name}: {e}")
            import traceback
            traceback.print_exc()
            return {"task_id": task_dir.name, "status": "error", "error": str(e)}


async def main_async(
    dataset_path: Path,
    docker_image: str,
    max_workers: int,
    max_retries: int,
    lm_config: Optional[LMConfig],
    data_filter: Optional[list[str]],
    force: bool = False,
    reject_inputs_mode: bool = False,
):
    """Main async orchestration."""
    async with DockerContainerManager(image=docker_image) as container:
        translator = TestTranslator(lm_config=lm_config)
        validator = TestValidator(container=container)

        # Find all task directories
        task_dirs = sorted(dataset_path.glob("verina_*"))

        # Filter if specified
        if data_filter:
            task_dirs = [d for d in task_dirs if d.name in data_filter]

        # Find tasks that need processing
        if reject_inputs_mode:
            # Process reject_inputs.json files
            source_file = "reject_inputs.json"
            target_file = "coq_reject_inputs.json"
            mode_name = "reject inputs"
        else:
            # Process test.json files
            source_file = "test.json"
            target_file = "coq_test.json"
            mode_name = "tests"

        if force:
            pending_tasks = [d for d in task_dirs if (d / source_file).exists() and (d / "task.v").exists()]
        else:
            pending_tasks = [
                d for d in task_dirs
                if (d / source_file).exists()
                and (d / "task.v").exists()
                and not (d / target_file).exists()
            ]

        logger.info(f"Found {len(pending_tasks)} {mode_name} to process out of {len(task_dirs)} total")

        if not pending_tasks:
            logger.info(f"No {mode_name} to process")
            return []

        # Process with parallelization
        semaphore = asyncio.Semaphore(max_workers)

        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console,
        ) as progress:
            task = progress.add_task(
                f"Processing {len(pending_tasks)} {mode_name}...",
                total=len(pending_tasks),
            )

            async def process_with_progress(task_dir):
                if reject_inputs_mode:
                    result = await process_reject_inputs(
                        task_dir, translator, validator, semaphore, max_retries, force
                    )
                else:
                    result = await process_single_task(
                        task_dir, translator, validator, semaphore, max_retries, force
                    )
                progress.advance(task)
                return result

            results = await asyncio.gather(
                *[process_with_progress(d) for d in pending_tasks],
                return_exceptions=True,
            )

        # Report results
        success_count = sum(1 for r in results if isinstance(r, dict) and r.get("status") == "success")
        failed_count = sum(1 for r in results if isinstance(r, dict) and r.get("status") == "failed")
        error_count = sum(1 for r in results if isinstance(r, dict) and r.get("status") == "error")
        skipped_count = sum(1 for r in results if isinstance(r, dict) and r.get("status") == "skipped")

        console.print(f"\n[bold]Results ({mode_name}):[/bold]")
        console.print(f"  [green]Success: {success_count}[/green]")
        console.print(f"  [red]Failed: {failed_count}[/red]")
        console.print(f"  [yellow]Errors: {error_count}[/yellow]")
        console.print(f"  [dim]Skipped: {skipped_count}[/dim]")

        # Log failed tasks
        for r in results:
            if isinstance(r, dict) and r.get("status") == "failed":
                logger.warning(f"Failed: {r['task_id']}: {r.get('error', 'unknown')}")
            elif isinstance(r, dict) and r.get("status") == "error":
                logger.error(f"Error: {r['task_id']}: {r.get('error', 'unknown')}")

        return results


app = typer.Typer(help="Translate Lean tests to Coq test format")


@app.command()
def translate(
    dataset_path: Path = typer.Option(
        DATASETS_DIR,
        "--dataset", "-d",
        help="Path to dataset directory",
    ),
    docker_image: str = typer.Option(
        "verina-coq",
        "--docker-image",
        help="Docker image for Coq compilation",
    ),
    max_workers: int = typer.Option(
        4,
        "--workers", "-w",
        help="Maximum parallel compilations",
    ),
    max_retries: int = typer.Option(
        3,
        "--retries", "-r",
        help="Maximum LLM refinement attempts per task",
    ),
    provider: str = typer.Option(
        "anthropic",
        "--provider",
        help="LLM provider (openai, anthropic)",
    ),
    model: str = typer.Option(
        "claude-sonnet-4-5-20250929",
        "--model", "-m",
        help="LLM model name",
    ),
    data_filter: str = typer.Option(
        "",
        "--filter", "-f",
        help="Comma-separated task IDs to process (empty = all)",
    ),
    dry_run: bool = typer.Option(
        False,
        "--dry-run",
        help="Print what would be done without executing",
    ),
    force: bool = typer.Option(
        False,
        "--force",
        help="Overwrite existing coq_test.json files",
    ),
    no_llm: bool = typer.Option(
        False,
        "--no-llm",
        help="Disable LLM (use simple conversion only)",
    ),
    reject_inputs: bool = typer.Option(
        False,
        "--reject-inputs",
        help="Convert reject_inputs.json instead of test.json",
    ),
):
    """Translate Lean tests to Coq format with type-check validation."""
    # Parse filter
    filter_list = [f.strip() for f in data_filter.split(",") if f.strip()] if data_filter else None

    # Determine source/target files based on mode
    if reject_inputs:
        source_file = "reject_inputs.json"
        target_file = "coq_reject_inputs.json"
        mode_name = "reject inputs"
    else:
        source_file = "test.json"
        target_file = "coq_test.json"
        mode_name = "tests"

    if dry_run:
        task_dirs = sorted(dataset_path.glob("verina_*"))
        if filter_list:
            task_dirs = [d for d in task_dirs if d.name in filter_list]

        if force:
            pending = [d.name for d in task_dirs if (d / source_file).exists() and (d / "task.v").exists()]
        else:
            pending = [
                d.name for d in task_dirs
                if (d / source_file).exists()
                and (d / "task.v").exists()
                and not (d / target_file).exists()
            ]

        console.print(f"[bold]Dry run mode ({mode_name})[/bold]")
        console.print(f"Would process {len(pending)} tasks:")
        for name in pending[:20]:
            console.print(f"  - {name}")
        if len(pending) > 20:
            console.print(f"  ... and {len(pending) - 20} more")
        return

    # Setup LLM config
    lm_config = None if no_llm else LMConfig(provider=provider, model_name=model)

    # Run async main
    asyncio.run(main_async(
        dataset_path=dataset_path,
        docker_image=docker_image,
        max_workers=max_workers,
        max_retries=max_retries,
        lm_config=lm_config,
        data_filter=filter_list,
        force=force,
        reject_inputs_mode=reject_inputs,
    ))


if __name__ == "__main__":
    app()
