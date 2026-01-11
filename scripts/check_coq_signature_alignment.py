#!/usr/bin/env python3
"""Check alignment between task.json coq_signature and task.v signature.

This script verifies that:
1. The function name in task.v matches coq_signature.name
2. Parameter names and types match coq_signature.parameters
3. Return type matches coq_signature.return_type

Usage:
    uv run python scripts/check_coq_signature_alignment.py
    uv run python scripts/check_coq_signature_alignment.py --filter verina_basic_1
    uv run python scripts/check_coq_signature_alignment.py --fix  # Auto-fix mismatches
"""

import json
import re
import sys
from pathlib import Path
from typing import Optional, Tuple, List

import typer
from rich.console import Console
from rich.table import Table

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from verina.dataset.schema import Signature, Parameter

console = Console()

# Project root
ROOT_DIR = Path(__file__).parent.parent
DATASETS_DIR = ROOT_DIR / "datasets" / "verina"


def parse_coq_definition(content: str, func_name: str) -> Optional[Tuple[str, List[Tuple[str, str]], str]]:
    """Parse a Coq Definition to extract signature components.

    Returns: (name, [(param_name, param_type), ...], return_type) or None if not found
    """
    # Pattern to match: Definition func_name (param1 : Type1) (param2 : Type2) ... : ReturnType :=
    # We need to find the main function definition (not _precond, _postcond)
    pattern = rf"Definition\s+({re.escape(func_name)})\s+((?:\([^)]+\)\s*)*)\([^)]*h_precond[^)]*\)\s*:\s*([^:=]+)\s*:="

    match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
    if not match:
        # Try simpler pattern without h_precond (for checking)
        pattern2 = rf"Definition\s+({re.escape(func_name)})\s+((?:\([^)]+\)\s*)+):\s*([^:=]+)\s*:="
        match = re.search(pattern2, content, re.MULTILINE | re.DOTALL)
        if not match:
            return None

    name = match.group(1)
    params_str = match.group(2).strip()
    return_type = match.group(3).strip()

    # Parse parameters: (a : Z) (b : Z) -> [(a, Z), (b, Z)]
    params = []
    param_pattern = r"\((\w+)\s*:\s*([^)]+)\)"
    for param_match in re.finditer(param_pattern, params_str):
        param_name = param_match.group(1)
        param_type = param_match.group(2).strip()
        # Skip h_precond parameter
        if param_name != "h_precond":
            params.append((param_name, param_type))

    return name, params, return_type


def check_alignment(task_dir: Path) -> dict:
    """Check if task.json coq_signature aligns with task.v.

    Returns dict with:
        - task_id: str
        - status: "aligned" | "misaligned" | "missing_file" | "no_coq_signature"
        - issues: list of issue descriptions
    """
    task_json_path = task_dir / "task.json"
    task_v_path = task_dir / "task.v"

    result = {
        "task_id": task_dir.name,
        "status": "aligned",
        "issues": [],
    }

    # Check files exist
    if not task_json_path.exists():
        result["status"] = "missing_file"
        result["issues"].append("task.json not found")
        return result

    if not task_v_path.exists():
        result["status"] = "missing_file"
        result["issues"].append("task.v not found")
        return result

    # Load task.json
    try:
        task_json = json.loads(task_json_path.read_text())
    except json.JSONDecodeError as e:
        result["status"] = "error"
        result["issues"].append(f"Invalid JSON: {e}")
        return result

    # Check coq_signature exists
    if "coq_signature" not in task_json:
        result["status"] = "no_coq_signature"
        result["issues"].append("No coq_signature in task.json")
        return result

    coq_sig = Signature(**task_json["coq_signature"])

    # Load task.v
    task_v_content = task_v_path.read_text()

    # Parse the main function definition
    parsed = parse_coq_definition(task_v_content, coq_sig.name)

    if parsed is None:
        result["status"] = "misaligned"
        result["issues"].append(f"Could not find Definition {coq_sig.name} in task.v")
        return result

    actual_name, actual_params, actual_return = parsed

    # Check function name
    if actual_name != coq_sig.name:
        result["status"] = "misaligned"
        result["issues"].append(f"Name mismatch: JSON={coq_sig.name}, task.v={actual_name}")

    # Check parameters
    expected_params = [(p.param_name, p.param_type) for p in coq_sig.parameters]

    if len(actual_params) != len(expected_params):
        result["status"] = "misaligned"
        result["issues"].append(
            f"Parameter count mismatch: JSON={len(expected_params)}, task.v={len(actual_params)}"
        )
    else:
        for i, ((exp_name, exp_type), (act_name, act_type)) in enumerate(zip(expected_params, actual_params)):
            if exp_name != act_name:
                result["status"] = "misaligned"
                result["issues"].append(f"Param {i} name mismatch: JSON={exp_name}, task.v={act_name}")
            # Normalize types for comparison (strip parens, whitespace)
            exp_type_norm = exp_type.strip().strip("()")
            act_type_norm = act_type.strip().strip("()")
            if exp_type_norm != act_type_norm:
                result["status"] = "misaligned"
                result["issues"].append(f"Param {exp_name} type mismatch: JSON={exp_type}, task.v={act_type}")

    # Check return type
    exp_return_norm = coq_sig.return_type.strip().strip("()")
    act_return_norm = actual_return.strip().strip("()")
    if exp_return_norm != act_return_norm:
        result["status"] = "misaligned"
        result["issues"].append(f"Return type mismatch: JSON={coq_sig.return_type}, task.v={actual_return}")

    return result


def check_all_tasks(dataset_path: Path, data_filter: Optional[List[str]] = None) -> List[dict]:
    """Check alignment for all tasks in the dataset."""
    task_dirs = sorted(dataset_path.glob("verina_*"))

    if data_filter:
        task_dirs = [d for d in task_dirs if d.name in data_filter]

    results = []
    for task_dir in task_dirs:
        result = check_alignment(task_dir)
        results.append(result)

    return results


app = typer.Typer(help="Check alignment between task.json coq_signature and task.v")


@app.command()
def check(
    dataset_path: Path = typer.Option(
        DATASETS_DIR,
        "--dataset", "-d",
        help="Path to dataset directory",
    ),
    data_filter: str = typer.Option(
        "",
        "--filter", "-f",
        help="Comma-separated task IDs to check (empty = all)",
    ),
    show_all: bool = typer.Option(
        False,
        "--all", "-a",
        help="Show all results (including aligned)",
    ),
    json_output: bool = typer.Option(
        False,
        "--json",
        help="Output as JSON",
    ),
):
    """Check alignment between task.json coq_signature and task.v."""
    # Parse filter
    filter_list = [f.strip() for f in data_filter.split(",") if f.strip()] if data_filter else None

    results = check_all_tasks(dataset_path, filter_list)

    if json_output:
        import json
        print(json.dumps(results, indent=2))
        return

    # Count by status
    aligned = sum(1 for r in results if r["status"] == "aligned")
    misaligned = sum(1 for r in results if r["status"] == "misaligned")
    missing = sum(1 for r in results if r["status"] == "missing_file")
    no_sig = sum(1 for r in results if r["status"] == "no_coq_signature")
    errors = sum(1 for r in results if r["status"] == "error")

    console.print(f"\n[bold]Signature Alignment Check[/bold]")
    console.print(f"  [green]Aligned: {aligned}[/green]")
    console.print(f"  [red]Misaligned: {misaligned}[/red]")
    console.print(f"  [yellow]Missing files: {missing}[/yellow]")
    console.print(f"  [dim]No coq_signature: {no_sig}[/dim]")
    console.print(f"  [red]Errors: {errors}[/red]")

    # Show details for non-aligned
    issues_to_show = [r for r in results if r["status"] != "aligned"]
    if show_all:
        issues_to_show = results

    if issues_to_show:
        console.print(f"\n[bold]Details:[/bold]")
        table = Table(show_header=True, header_style="bold")
        table.add_column("Task ID")
        table.add_column("Status")
        table.add_column("Issues")

        for r in issues_to_show:
            status_style = {
                "aligned": "green",
                "misaligned": "red",
                "missing_file": "yellow",
                "no_coq_signature": "dim",
                "error": "red",
            }.get(r["status"], "white")

            table.add_row(
                r["task_id"],
                f"[{status_style}]{r['status']}[/{status_style}]",
                "\n".join(r["issues"]) if r["issues"] else "-",
            )

        console.print(table)


@app.command()
def report(
    dataset_path: Path = typer.Option(
        DATASETS_DIR,
        "--dataset", "-d",
        help="Path to dataset directory",
    ),
    output: Path = typer.Option(
        None,
        "--output", "-o",
        help="Output file for report (default: stdout)",
    ),
):
    """Generate a detailed alignment report."""
    results = check_all_tasks(dataset_path)

    lines = []
    lines.append("# Coq Signature Alignment Report\n")

    # Summary
    aligned = sum(1 for r in results if r["status"] == "aligned")
    misaligned = sum(1 for r in results if r["status"] == "misaligned")
    total = len(results)

    lines.append(f"## Summary")
    lines.append(f"- Total tasks: {total}")
    lines.append(f"- Aligned: {aligned} ({100*aligned/total:.1f}%)")
    lines.append(f"- Misaligned: {misaligned} ({100*misaligned/total:.1f}%)")
    lines.append("")

    # Misaligned details
    if misaligned > 0:
        lines.append("## Misaligned Tasks\n")
        for r in results:
            if r["status"] == "misaligned":
                lines.append(f"### {r['task_id']}")
                for issue in r["issues"]:
                    lines.append(f"- {issue}")
                lines.append("")

    report_text = "\n".join(lines)

    if output:
        output.write_text(report_text)
        console.print(f"Report written to {output}")
    else:
        console.print(report_text)


if __name__ == "__main__":
    app()
