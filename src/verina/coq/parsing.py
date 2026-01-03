"""Coq specific parsing implementation.

This module provides the Coq-specific parser for benchmark data files,
implementing the ITPParser interface.

Coq uses block comments (* ... *) instead of Lean's single-line comments (--).
Benchmark markers are in the format:
    (* !benchmark @start section_name [args] *)
    ...content...
    (* !benchmark @end section_name *)
"""

from typing import Dict, List, Optional
import re

from pydantic import BaseModel

from verina.itp.base import ITPBenchmarkData, ITPBenchmarkDataSection, ITPParser


class BenchmarkCoqDataSection(BaseModel):
    """A section of Coq benchmark data with name, args, and content."""
    name: str
    args: Dict[str, str]
    content: str


class BenchmarkCoqData(BaseModel):
    """Coq-specific parsed benchmark data.

    This extends ITPBenchmarkData with Coq-specific defaults and behavior.
    """
    task_imports: str = ""
    solution_imports: str = ""

    task_aux: str = ""
    solution_aux: str = ""
    code_aux: str = ""
    precond_aux: str = ""
    postcond_aux: str = ""
    proof_aux: str = ""

    code: str = ""
    precond: str = "True"  # default precond
    postcond: str = ""
    proof: str = "admit."  # default: incomplete proof

    @staticmethod
    def from_sections(sections: List[BenchmarkCoqDataSection]) -> "BenchmarkCoqData":
        """Build BenchmarkCoqData from a list of parsed sections."""
        coq_data = BenchmarkCoqData(
            task_imports="",
            solution_imports="",
            task_aux="",
            solution_aux="",
            code_aux="",
            precond_aux="",
            postcond_aux="",
            proof_aux="",
            code="",
            precond="True",
            postcond="",
            proof="admit.",
        )

        for section in sections:
            if section.name == "import":
                if section.args.get("type") == "task":
                    coq_data.task_imports += f"\n{section.content}\n"
                elif section.args.get("type") == "solution":
                    coq_data.solution_imports += f"\n{section.content}\n"
            elif section.name in coq_data.model_fields:
                if section.content.strip():
                    setattr(coq_data, section.name, section.content)
            else:
                raise ValueError(f"Unknown section name: {section.name}")

        return coq_data

    def to_itp_data(self) -> ITPBenchmarkData:
        """Convert to generic ITPBenchmarkData."""
        return ITPBenchmarkData(
            task_imports=self.task_imports,
            solution_imports=self.solution_imports,
            task_aux=self.task_aux,
            solution_aux=self.solution_aux,
            code_aux=self.code_aux,
            precond_aux=self.precond_aux,
            postcond_aux=self.postcond_aux,
            proof_aux=self.proof_aux,
            code=self.code,
            precond=self.precond,
            postcond=self.postcond,
            proof=self.proof,
        )


class CoqParser(ITPParser):
    """Coq-specific parser implementing ITPParser interface.

    Parses Coq source files with benchmark markers in the format:
    (* !benchmark @start section_name [args] *)
    ...content...
    (* !benchmark @end section_name *)
    """

    # Regex patterns for Coq benchmark markers
    START_PATTERN = re.compile(r'\(\*\s*!benchmark\s+@start\s+(\w+)\s*(.*?)\s*\*\)')
    END_PATTERN = re.compile(r'\(\*\s*!benchmark\s+@end\s+(\w+)\s*\*\)')

    def get_comment_start_marker(self) -> str:
        """Return Coq block comment start marker."""
        return "(*"

    def get_comment_end_marker(self) -> str:
        """Return Coq block comment end marker."""
        return "*)"

    def get_benchmark_marker(self) -> str:
        """Return the benchmark marker string."""
        return "!benchmark"

    def parse_benchmark_data(self, raw_content: str) -> ITPBenchmarkData:
        """Parse raw Coq source into benchmark data sections.

        Args:
            raw_content: Raw content of the Coq source file.

        Returns:
            Parsed ITPBenchmarkData with all sections extracted.
        """
        coq_data = parse_benchmark_coq_data(raw_content)
        return coq_data.to_itp_data()

    def parse_coq_data(self, raw_content: str) -> BenchmarkCoqData:
        """Parse raw Coq source into Coq-specific benchmark data.

        This method returns the Coq-specific data type.

        Args:
            raw_content: Raw content of the Coq source file.

        Returns:
            Parsed BenchmarkCoqData with all sections extracted.
        """
        return parse_benchmark_coq_data(raw_content)


def parse_benchmark_coq_data(raw_coq_data: str) -> BenchmarkCoqData:
    """Parse Coq benchmark data from raw file content.

    This function parses Coq source files that use the benchmark marker format:
    (* !benchmark @start section_name [type=value] *)
    ...section content...
    (* !benchmark @end section_name *)

    Args:
        raw_coq_data: Raw content of the Coq file.

    Returns:
        Parsed BenchmarkCoqData with all sections extracted.
    """
    sections = []
    current_section: Optional[BenchmarkCoqDataSection] = None
    content_buffer = []

    lines = raw_coq_data.splitlines()

    for line in lines:
        # Check for benchmark start marker
        start_match = CoqParser.START_PATTERN.search(line)
        if start_match:
            section_name = start_match.group(1)
            args_str = start_match.group(2).strip()

            # Parse arguments
            args = {}
            if args_str:
                arg_parts = args_str.split()
                for arg in arg_parts:
                    if "=" in arg:
                        key, value = arg.split("=", 1)
                        args[key] = value

            # Start new section
            if current_section is not None:
                raise ValueError(
                    f"Nested sections not supported: found @start {section_name} "
                    f"while in section {current_section.name}"
                )

            current_section = BenchmarkCoqDataSection(
                name=section_name, args=args, content=""
            )
            content_buffer = []
            continue

        # Check for benchmark end marker
        end_match = CoqParser.END_PATTERN.search(line)
        if end_match:
            end_section = end_match.group(1)

            if current_section is None:
                raise ValueError(f"Found @end {end_section} without matching @start")

            if end_section != current_section.name:
                raise ValueError(
                    f"Mismatched section end: expected {current_section.name}, "
                    f"found {end_section}"
                )

            # Save section content
            current_section.content = "\n".join(content_buffer)
            sections.append(current_section)
            current_section = None
            content_buffer = []
            continue

        # Accumulate content if inside a section
        if current_section is not None:
            content_buffer.append(line)

    if current_section is not None:
        raise ValueError(f"Unclosed section: {current_section.name}")

    return BenchmarkCoqData.from_sections(sections)


# Export public API
__all__ = [
    "CoqParser",
    "BenchmarkCoqData",
    "BenchmarkCoqDataSection",
    "parse_benchmark_coq_data",
]
