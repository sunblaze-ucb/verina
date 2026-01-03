#!/usr/bin/env python3
"""Translate Lean signatures to Coq task.v files with compilation validation.

This script:
1. Finds all task.json files missing task.v
2. Translates Lean signatures to Coq types
3. Generates minimal task.v skeletons
4. Validates compilation using a long-running Docker container
5. Refines with LLM on compilation errors

Usage:
    uv run python scripts/translate_to_coq.py
    uv run python scripts/translate_to_coq.py --dry-run
    uv run python scripts/translate_to_coq.py --filter verina_basic_1,verina_basic_2
"""

import asyncio
import json
import logging
import re
import sys
from pathlib import Path
from typing import Optional, Tuple

import typer
from dotenv import load_dotenv
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from verina.coq.types import lean_type_to_coq, get_coq_imports_for_types
from verina.dataset.schema import Signature, Parameter
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
        container_name: str = "verina-coq-translator",
    ):
        self.image = image
        self.container_name = container_name
        self.container_id: Optional[str] = None

    async def start(self) -> str:
        """Start a long-running container, return container ID."""
        # First, remove any existing container with the same name
        await self._run_docker(["rm", "-f", self.container_name], ignore_errors=True)

        # Start new container with workspace mounted
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
        """Execute coqc inside the running container.

        Returns (success, output).
        """
        relative_path = file_path.relative_to(ROOT_DIR)
        # Use bash -lc to get proper environment (opam setup)
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


class SignatureTranslator:
    """Translates Lean signatures to Coq task.v files."""

    def translate_signature(self, lean_sig: Signature) -> Signature:
        """Convert Lean signature to Coq signature."""
        coq_params = []
        for param in lean_sig.parameters:
            coq_type = lean_type_to_coq(param.param_type)
            coq_params.append(Parameter(param_name=param.param_name, param_type=coq_type))

        coq_return = lean_type_to_coq(lean_sig.return_type)
        return Signature(
            name=lean_sig.name,
            parameters=coq_params,
            return_type=coq_return,
        )

    def get_imports(self, coq_sig: Signature) -> str:
        """Get required imports for the Coq signature."""
        types = [p.param_type for p in coq_sig.parameters]
        types.append(coq_sig.return_type)
        return get_coq_imports_for_types(types)

    def get_placeholder(self, coq_type: str) -> str:
        """Get a placeholder value for a Coq type."""
        coq_type_lower = coq_type.lower()
        # Check option first (before checking for other types inside option)
        if "option" in coq_type_lower:
            return "None"
        elif "list" in coq_type_lower:
            return "[]"
        elif "z" in coq_type_lower:
            return "0%Z"
        elif "nat" in coq_type_lower:
            return "0"
        elif "bool" in coq_type_lower:
            return "true"
        elif "string" in coq_type_lower:
            return '""'
        elif "ascii" in coq_type_lower:
            return '"a"%char'
        elif "*" in coq_type_lower:
            # Product type - return a pair of placeholders
            return "(0, 0)"
        else:
            return "(* placeholder *) tt"

    def render_params(self, coq_sig: Signature) -> str:
        """Render parameter list: (a : Z) (b : Z)"""
        return " ".join(f"({p.param_name} : {p.param_type})" for p in coq_sig.parameters)

    def render_param_names(self, coq_sig: Signature) -> str:
        """Render just the parameter names: a b"""
        return " ".join(p.param_name for p in coq_sig.parameters)

    def generate_task_v(self, coq_sig: Signature) -> str:
        """Generate a minimal task.v skeleton."""
        name = coq_sig.name
        imports = self.get_imports(coq_sig)
        params = self.render_params(coq_sig)
        param_names = self.render_param_names(coq_sig)
        return_type = coq_sig.return_type
        placeholder = self.get_placeholder(return_type)

        return f"""(* !benchmark @start import type=task *)
{imports}
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition {name}_precond_dec {params} : bool := true.
(* !benchmark @end precond_aux *)

Definition {name}_precond {params} : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition {name} {params} (h_precond : {name}_precond {param_names}) : {return_type} :=
  (* !benchmark @start code *)
  {placeholder}
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition {name}_postcond_dec {params} (result : {return_type}) : bool := true.
(* !benchmark @end postcond_aux *)

Definition {name}_postcond {params} (result : {return_type}) (h_precond : {name}_precond {param_names}) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem {name}_postcond_satisfied {params} (h_precond : {name}_precond {param_names}) :
    {name}_postcond {param_names} ({name} {param_names} h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
"""


REFINEMENT_PROMPT = """The following Coq code failed to compile. Fix it.

## Current Code:
```coq
{current_code}
```

## Compilation Error:
{error_message}

## Instructions:
1. Analyze the error message carefully
2. Fix the syntax or type errors
3. Ensure all required imports are present (ZArith for Z, Bool for bool, List for list, String for string, Ascii for ascii)
4. Preserve the benchmark marker structure exactly: (* !benchmark @start ... *) and (* !benchmark @end ... *)
5. Make sure types are correct: Z for integers, nat for natural numbers, bool for booleans
6. Ensure placeholder values match return types

Output ONLY the corrected Coq code, no explanations or markdown code blocks."""


class RefinementLoop:
    """Iteratively refine Coq code until it compiles."""

    def __init__(
        self,
        translator: SignatureTranslator,
        container: DockerContainerManager,
        lm_config: Optional[LMConfig] = None,
        max_retries: int = 3,
    ):
        self.translator = translator
        self.container = container
        self.lm_config = lm_config
        self.max_retries = max_retries
        self._lm = None

    @property
    def lm(self):
        """Lazy-load the LLM."""
        if self._lm is None and self.lm_config:
            import dspy
            self._lm = self.lm_config.get_model()
            dspy.configure(lm=self._lm)
        return self._lm

    async def translate_and_validate(
        self,
        task_dir: Path,
        lean_sig: Signature,
    ) -> Tuple[bool, str, int]:
        """Translate signature, compile, refine if needed.

        Returns: (success, final_code, attempts)
        """
        # Step 1: Translate signature
        coq_sig = self.translator.translate_signature(lean_sig)
        current_code = self.translator.generate_task_v(coq_sig)

        task_v_path = task_dir / "task.v"

        for attempt in range(self.max_retries + 1):
            # Step 2: Write to file and compile
            task_v_path.write_text(current_code)
            success, output = await self.container.exec_coqc(task_v_path)

            if success:
                return True, current_code, attempt + 1

            if attempt == self.max_retries:
                # Max retries reached
                logger.warning(f"Max retries reached for {task_dir.name}")
                # Save failed version for inspection
                failed_path = task_dir / "task.v.failed"
                failed_path.write_text(f"(* Compilation Error:\n{output}\n*)\n\n{current_code}")
                task_v_path.unlink()  # Remove failed task.v
                return False, current_code, attempt + 1

            # Step 3: Refine with LLM
            if self.lm:
                logger.info(f"Attempt {attempt + 1} failed for {task_dir.name}, refining...")
                current_code = await self._refine_with_llm(current_code, output)
            else:
                # No LLM, can't refine - save failed version for inspection
                logger.warning(f"No LLM configured, cannot refine {task_dir.name}")
                logger.debug(f"Compilation error: {output[:500]}")
                failed_path = task_dir / "task.v.failed"
                failed_path.write_text(f"(* Compilation Error:\n{output}\n*)\n\n{current_code}")
                task_v_path.unlink(missing_ok=True)
                return False, current_code, attempt + 1

        return False, current_code, self.max_retries + 1

    async def _refine_with_llm(self, code: str, error: str) -> str:
        """Ask LLM to fix compilation errors."""
        import dspy

        prompt = REFINEMENT_PROMPT.format(
            current_code=code,
            error_message=error[:2000],  # Truncate long errors
        )

        # Use dspy for completion
        response = self.lm(prompt)
        if response and len(response) > 0:
            refined = response[0]
            # Clean up response - extract code if wrapped in markdown
            refined = self._extract_coq_code(refined)
            return refined
        return code

    def _extract_coq_code(self, text: str) -> str:
        """Extract Coq code from LLM response."""
        # Remove markdown code blocks if present
        code_block_pattern = r"```(?:coq)?\s*(.*?)```"
        match = re.search(code_block_pattern, text, re.DOTALL)
        if match:
            return match.group(1).strip()
        return text.strip()


async def process_single_task(
    task_dir: Path,
    refinement_loop: RefinementLoop,
    semaphore: asyncio.Semaphore,
) -> dict:
    """Process a single task directory."""
    async with semaphore:
        task_json_path = task_dir / "task.json"
        task_v_path = task_dir / "task.v"

        # Skip if task.v already exists
        if task_v_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "exists"}

        # Skip if no task.json
        if not task_json_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_json"}

        try:
            # Load task.json
            task_json = json.loads(task_json_path.read_text())

            # Check if signature exists
            if "signature" not in task_json:
                return {"task_id": task_dir.name, "status": "skipped", "reason": "no_signature"}

            lean_sig = Signature(**task_json["signature"])

            # Translate and validate
            success, final_code, attempts = await refinement_loop.translate_and_validate(
                task_dir, lean_sig
            )

            if success:
                # Update task.json with coq_file and coq_signature
                coq_sig = refinement_loop.translator.translate_signature(lean_sig)
                task_json["coq_file"] = "./task.v"
                task_json["coq_signature"] = {
                    "name": coq_sig.name,
                    "parameters": [{"param_name": p.param_name, "param_type": p.param_type} for p in coq_sig.parameters],
                    "return_type": coq_sig.return_type,
                }
                task_json_path.write_text(json.dumps(task_json, indent=4))

            return {
                "task_id": task_dir.name,
                "status": "success" if success else "failed",
                "attempts": attempts,
            }

        except Exception as e:
            logger.error(f"Error processing {task_dir.name}: {e}")
            return {"task_id": task_dir.name, "status": "error", "error": str(e)}


async def main_async(
    dataset_path: Path,
    docker_image: str,
    max_workers: int,
    max_retries: int,
    lm_config: Optional[LMConfig],
    data_filter: Optional[list[str]],
):
    """Main async orchestration."""
    async with DockerContainerManager(image=docker_image) as container:
        translator = SignatureTranslator()
        refinement_loop = RefinementLoop(
            translator=translator,
            container=container,
            lm_config=lm_config,
            max_retries=max_retries,
        )

        # Find all task directories
        task_dirs = sorted(dataset_path.glob("verina_*"))

        # Filter if specified
        if data_filter:
            task_dirs = [d for d in task_dirs if d.name in data_filter]

        # Find pending tasks (no task.v)
        pending_tasks = [d for d in task_dirs if not (d / "task.v").exists()]

        logger.info(f"Found {len(pending_tasks)} tasks without task.v out of {len(task_dirs)} total")

        if not pending_tasks:
            logger.info("No tasks to process")
            return []

        # Process with parallelization
        semaphore = asyncio.Semaphore(max_workers)

        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console,
        ) as progress:
            task = progress.add_task(
                f"Processing {len(pending_tasks)} tasks...",
                total=len(pending_tasks),
            )

            async def process_with_progress(task_dir):
                result = await process_single_task(task_dir, refinement_loop, semaphore)
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

        console.print(f"\n[bold]Results:[/bold]")
        console.print(f"  [green]Success: {success_count}[/green]")
        console.print(f"  [red]Failed: {failed_count}[/red]")
        console.print(f"  [yellow]Errors: {error_count}[/yellow]")
        console.print(f"  [dim]Skipped: {skipped_count}[/dim]")

        # Log failed tasks
        for r in results:
            if isinstance(r, dict) and r.get("status") == "failed":
                logger.warning(f"Failed: {r['task_id']} after {r.get('attempts', '?')} attempts")
            elif isinstance(r, dict) and r.get("status") == "error":
                logger.error(f"Error: {r['task_id']}: {r.get('error', 'unknown')}")

        return results


app = typer.Typer(help="Translate Lean signatures to Coq task.v files")


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
        8,
        "--workers", "-w",
        help="Maximum parallel compilations",
    ),
    max_retries: int = typer.Option(
        3,
        "--retries", "-r",
        help="Maximum LLM refinement attempts per task",
    ),
    provider: str = typer.Option(
        "openai",
        "--provider",
        help="LLM provider (openai, anthropic, local)",
    ),
    model: str = typer.Option(
        "gpt-4o-mini",
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
    no_llm: bool = typer.Option(
        False,
        "--no-llm",
        help="Disable LLM refinement (only try initial translation)",
    ),
):
    """Translate Lean signatures to Coq task.v files with validation."""
    # Parse filter
    filter_list = [f.strip() for f in data_filter.split(",") if f.strip()] if data_filter else None

    if dry_run:
        task_dirs = sorted(dataset_path.glob("verina_*"))
        if filter_list:
            task_dirs = [d for d in task_dirs if d.name in filter_list]
        pending = [d.name for d in task_dirs if not (d / "task.v").exists()]
        console.print(f"[bold]Dry run mode[/bold]")
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
    ))


if __name__ == "__main__":
    app()
