#!/usr/bin/env python3
"""Translate Lean ground truth (code & spec) to Coq using Claude Opus 4.5.

This script:
1. Reads Lean task.lean files and extracts code/spec (not proof)
2. Uses Claude Opus 4.5 to translate to Coq
3. Compiles and refines up to 5 times until it compiles
4. Never changes the signature (from task.json coq_signature)
5. Preserves benchmark marker structure

Usage:
    uv run python scripts/translate_lean_to_coq.py
    uv run python scripts/translate_lean_to_coq.py --filter verina_basic_1
    uv run python scripts/translate_lean_to_coq.py --max-retries 5
    uv run python scripts/translate_lean_to_coq.py --dry-run
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
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from verina.lean.parsing import LeanParser
from verina.coq.parsing import CoqParser
from verina.coq.types import get_coq_imports_for_types
from verina.dataset.schema import Signature
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

    async def exec_coqc(self, file_path: Path, timeout: int = 120) -> Tuple[bool, str]:
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


TRANSLATION_PROMPT = """You are an expert at translating Lean 4 code to Coq/Rocq.

## Task
Translate the following Lean 4 ground truth (code and specification) to Coq.

## Lean Ground Truth

### Function Signature (Lean)
```lean
{lean_signature}
```

### Coq Signature (DO NOT CHANGE)
```coq
{coq_signature}
```

### Lean Code (solution_aux + code_aux + code)
```lean
{lean_code}
```

### Lean Precondition (precond_aux + precond)
```lean
{lean_precond}
```

### Lean Postcondition (postcond_aux + postcond)
```lean
{lean_postcond}
```

## Description
{description}

## Instructions
1. Translate the Lean code and specification to Coq
2. NEVER change the function signature - use exactly: {func_name} with parameters {param_list} returning {return_type}
3. Translate Lean types to Coq: Int→Z, Nat→nat, Bool→bool, List→list, Array→list, String→string, Char→ascii
4. Translate Lean operators: ∧→/\\, ∨→\\/, ¬→~, →→->, ↔→<->, ≠→<>, ≤→<=, ≥→>=
5. Use Z scope for integers: (x + y)%Z, (x * y)%Z, (x <? y)%Z for comparisons returning bool
6. List syntax: [] for empty, [a; b; c] for lists, (hd :: tl) for cons
7. For decidable precond/postcond, also provide _dec versions returning bool
8. DO NOT include any proof - leave proof section as "admit."

## Output Format
Return ONLY the content for each section (no markdown code blocks, no explanations):

===SOLUTION_IMPORTS===
(* additional imports needed *)

===SOLUTION_AUX===
(* helper definitions *)

===PRECOND_AUX===
(* precondition helpers, including _dec version *)

===PRECOND===
(* precondition Prop - must be valid in context: Definition {func_name}_precond {params} : Prop := *)

===CODE_AUX===
(* code helpers *)

===CODE===
(* code body - must be valid in context: Definition {func_name} {params} (h_precond : ...) : {return_type} := *)

===POSTCOND_AUX===
(* postcondition helpers, including _dec version *)

===POSTCOND===
(* postcondition Prop - must be valid in context: Definition {func_name}_postcond {params} (result : {return_type}) (h_precond : ...) : Prop := *)
"""

REFINEMENT_PROMPT = """The Coq code failed to compile. Fix the errors while preserving the signature.

## Current Coq Code
```coq
{current_code}
```

## Compilation Error
{error_message}

## Coq Signature (DO NOT CHANGE)
Function: {func_name}
Parameters: {param_list}
Return type: {return_type}

## Instructions
1. Fix the compilation errors
2. NEVER change the function signature
3. Ensure all types match: Z for integers, nat for naturals, bool for booleans
4. Ensure proper scoping: use %Z for integer operations
5. For list operations: use [a; b; c] syntax, not [a, b, c]
6. Preserve ALL benchmark markers: (* !benchmark @start ... *) and (* !benchmark @end ... *)

Return ONLY the sections that need fixing (use same format as before):
===SECTION_NAME===
content
"""


def extract_sections(response: str) -> dict:
    """Extract sections from LLM response."""
    sections = {}
    current_section = None
    current_content = []

    for line in response.split("\n"):
        if line.startswith("===") and line.endswith("==="):
            if current_section:
                sections[current_section] = "\n".join(current_content).strip()
            current_section = line.strip("=").strip()
            current_content = []
        elif current_section:
            current_content.append(line)

    if current_section:
        sections[current_section] = "\n".join(current_content).strip()

    return sections


def render_coq_file(
    coq_sig: Signature,
    imports: str,
    solution_imports: str,
    solution_aux: str,
    precond_aux: str,
    precond: str,
    code_aux: str,
    code: str,
    postcond_aux: str,
    postcond: str,
) -> str:
    """Render a complete task.v file with translated content."""
    name = coq_sig.name
    params = " ".join(f"({p.param_name} : {p.param_type})" for p in coq_sig.parameters)
    param_names = " ".join(p.param_name for p in coq_sig.parameters)
    return_type = coq_sig.return_type

    return f"""(* !benchmark @start import type=task *)
{imports}
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
{solution_imports}
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
{solution_aux}
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
{precond_aux}
(* !benchmark @end precond_aux *)

Definition {name}_precond {params} : Prop :=
  (* !benchmark @start precond *)
  {precond}
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
{code_aux}
(* !benchmark @end code_aux *)

Definition {name} {params} (h_precond : {name}_precond {param_names}) : {return_type} :=
  (* !benchmark @start code *)
  {code}
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
{postcond_aux}
(* !benchmark @end postcond_aux *)

Definition {name}_postcond {params} (result : {return_type}) (h_precond : {name}_precond {param_names}) : Prop :=
  (* !benchmark @start postcond *)
  {postcond}
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


class LeanToCoqTranslator:
    """Translates Lean ground truth to Coq using LLM."""

    def __init__(
        self,
        container: DockerContainerManager,
        lm_config: LMConfig,
        max_retries: int = 5,
    ):
        self.container = container
        self.lm_config = lm_config
        self.max_retries = max_retries
        self._lm = None
        self.lean_parser = LeanParser()
        self.coq_parser = CoqParser()

    @property
    def lm(self):
        """Lazy-load the LLM."""
        if self._lm is None:
            import dspy
            self._lm = self.lm_config.get_model()
            dspy.configure(lm=self._lm)
        return self._lm

    async def translate_task(self, task_dir: Path) -> Tuple[bool, str, int]:
        """Translate a single task from Lean to Coq.

        Returns: (success, final_code, attempts)
        """
        task_json_path = task_dir / "task.json"
        task_lean_path = task_dir / "task.lean"
        task_v_path = task_dir / "task.v"
        description_path = task_dir / "description.txt"

        # Load task.json
        task_json = json.loads(task_json_path.read_text())

        # Check if coq_signature exists
        if "coq_signature" not in task_json:
            return False, "No coq_signature in task.json", 0

        coq_sig = Signature(**task_json["coq_signature"])
        lean_sig = Signature(**task_json["signature"])

        # Parse Lean file
        lean_content = task_lean_path.read_text()
        lean_data = self.lean_parser.parse_lean_data(lean_content)

        # Load description
        description = description_path.read_text() if description_path.exists() else ""

        # Get base imports for Coq types
        types = [p.param_type for p in coq_sig.parameters] + [coq_sig.return_type]
        base_imports = get_coq_imports_for_types(types)

        # Build Lean signature string
        lean_params = " ".join(f"({p.param_name} : {p.param_type})" for p in lean_sig.parameters)
        lean_sig_str = f"def {lean_sig.name} {lean_params} : {lean_sig.return_type}"

        # Build Coq signature string
        coq_params = " ".join(f"({p.param_name} : {p.param_type})" for p in coq_sig.parameters)
        coq_sig_str = f"Definition {coq_sig.name} {coq_params} : {coq_sig.return_type}"

        # Combine aux sections with main content
        lean_code = f"{lean_data.solution_aux}\n{lean_data.code_aux}\n{lean_data.code}".strip()
        lean_precond = f"{lean_data.precond_aux}\n{lean_data.precond}".strip()
        lean_postcond = f"{lean_data.postcond_aux}\n{lean_data.postcond}".strip()

        # Initial translation prompt
        prompt = TRANSLATION_PROMPT.format(
            lean_signature=lean_sig_str,
            coq_signature=coq_sig_str,
            lean_code=lean_code,
            lean_precond=lean_precond,
            lean_postcond=lean_postcond,
            description=description,
            func_name=coq_sig.name,
            param_list=coq_params,
            return_type=coq_sig.return_type,
        )

        # Get initial translation
        response = self.lm(prompt)
        if not response or len(response) == 0:
            return False, "LLM returned empty response", 0

        sections = extract_sections(response[0])

        # Build initial Coq file
        current_code = render_coq_file(
            coq_sig=coq_sig,
            imports=base_imports,
            solution_imports=sections.get("SOLUTION_IMPORTS", ""),
            solution_aux=sections.get("SOLUTION_AUX", ""),
            precond_aux=sections.get("PRECOND_AUX", ""),
            precond=sections.get("PRECOND", "True"),
            code_aux=sections.get("CODE_AUX", ""),
            code=sections.get("CODE", "true (* placeholder *)"),
            postcond_aux=sections.get("POSTCOND_AUX", ""),
            postcond=sections.get("POSTCOND", "True"),
        )

        # Refinement loop
        for attempt in range(self.max_retries + 1):
            task_v_path.write_text(current_code)
            success, output = await self.container.exec_coqc(task_v_path)

            if success:
                logger.info(f"[{task_dir.name}] Compiled successfully on attempt {attempt + 1}")
                return True, current_code, attempt + 1

            if attempt == self.max_retries:
                logger.warning(f"[{task_dir.name}] Max retries ({self.max_retries}) reached")
                # Save failed version
                failed_path = task_dir / "task.v.translation_failed"
                failed_path.write_text(f"(* Compilation Error:\n{output}\n*)\n\n{current_code}")
                return False, current_code, attempt + 1

            # Refine with LLM
            logger.info(f"[{task_dir.name}] Attempt {attempt + 1} failed, refining...")

            refine_prompt = REFINEMENT_PROMPT.format(
                current_code=current_code,
                error_message=output[:3000],
                func_name=coq_sig.name,
                param_list=coq_params,
                return_type=coq_sig.return_type,
            )

            refine_response = self.lm(refine_prompt)
            if refine_response and len(refine_response) > 0:
                new_sections = extract_sections(refine_response[0])
                # Update only the sections that were returned
                for key, value in new_sections.items():
                    sections[key] = value

                current_code = render_coq_file(
                    coq_sig=coq_sig,
                    imports=base_imports,
                    solution_imports=sections.get("SOLUTION_IMPORTS", ""),
                    solution_aux=sections.get("SOLUTION_AUX", ""),
                    precond_aux=sections.get("PRECOND_AUX", ""),
                    precond=sections.get("PRECOND", "True"),
                    code_aux=sections.get("CODE_AUX", ""),
                    code=sections.get("CODE", "true (* placeholder *)"),
                    postcond_aux=sections.get("POSTCOND_AUX", ""),
                    postcond=sections.get("POSTCOND", "True"),
                )

        return False, current_code, self.max_retries + 1


async def process_single_task(
    task_dir: Path,
    translator: LeanToCoqTranslator,
    semaphore: asyncio.Semaphore,
) -> dict:
    """Process a single task directory."""
    async with semaphore:
        task_json_path = task_dir / "task.json"
        task_lean_path = task_dir / "task.lean"
        task_v_path = task_dir / "task.v"

        # Skip if no task.json or task.lean
        if not task_json_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_json"}
        if not task_lean_path.exists():
            return {"task_id": task_dir.name, "status": "skipped", "reason": "no_task_lean"}

        # Check if task.v already has ground truth (not just placeholder)
        if task_v_path.exists():
            content = task_v_path.read_text()
            # Check if it has actual code (not just "true" placeholder)
            if "TODO: ground truth" not in content and "placeholder" not in content.lower():
                return {"task_id": task_dir.name, "status": "skipped", "reason": "already_translated"}

        try:
            success, final_code, attempts = await translator.translate_task(task_dir)
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
    lm_config: LMConfig,
    data_filter: Optional[list[str]],
):
    """Main async orchestration."""
    async with DockerContainerManager(image=docker_image) as container:
        translator = LeanToCoqTranslator(
            container=container,
            lm_config=lm_config,
            max_retries=max_retries,
        )

        # Find all task directories
        task_dirs = sorted(dataset_path.glob("verina_*"))

        # Filter if specified
        if data_filter:
            task_dirs = [d for d in task_dirs if d.name in data_filter]

        logger.info(f"Processing {len(task_dirs)} tasks")

        # Process with parallelization
        semaphore = asyncio.Semaphore(max_workers)

        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TaskProgressColumn(),
            console=console,
        ) as progress:
            task = progress.add_task(
                f"Translating {len(task_dirs)} tasks...",
                total=len(task_dirs),
            )

            async def process_with_progress(task_dir):
                result = await process_single_task(task_dir, translator, semaphore)
                progress.advance(task)
                return result

            results = await asyncio.gather(
                *[process_with_progress(d) for d in task_dirs],
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


app = typer.Typer(help="Translate Lean ground truth to Coq using Claude Opus 4.5")


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
        help="Maximum parallel translations",
    ),
    max_retries: int = typer.Option(
        5,
        "--retries", "-r",
        help="Maximum refinement attempts per task",
    ),
    provider: str = typer.Option(
        "anthropic",
        "--provider",
        help="LLM provider",
    ),
    model: str = typer.Option(
        "claude-opus-4-5-20251101",
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
):
    """Translate Lean ground truth (code & spec) to Coq."""
    # Parse filter
    filter_list = [f.strip() for f in data_filter.split(",") if f.strip()] if data_filter else None

    if dry_run:
        task_dirs = sorted(dataset_path.glob("verina_*"))
        if filter_list:
            task_dirs = [d for d in task_dirs if d.name in filter_list]
        console.print(f"[bold]Dry run mode[/bold]")
        console.print(f"Would process {len(task_dirs)} tasks with:")
        console.print(f"  Model: {model}")
        console.print(f"  Max retries: {max_retries}")
        console.print(f"  Max workers: {max_workers}")
        for name in [d.name for d in task_dirs[:10]]:
            console.print(f"  - {name}")
        if len(task_dirs) > 10:
            console.print(f"  ... and {len(task_dirs) - 10} more")
        return

    # Setup LLM config
    lm_config = LMConfig(provider=provider, model_name=model)

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
