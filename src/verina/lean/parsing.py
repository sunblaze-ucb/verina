"""Lean 4 specific parsing implementation.

This module provides the Lean-specific parser for benchmark data files,
implementing the ITPParser interface.
"""

from typing import Dict, List, Optional

from pydantic import BaseModel

from verina.itp.base import ITPBenchmarkData, ITPBenchmarkDataSection, ITPParser


class BenchmarkLeanDataSection(BaseModel):
    """A section of Lean benchmark data with name, args, and content.

    This is an alias for ITPBenchmarkDataSection for backward compatibility.
    """
    name: str
    args: Dict[str, str]
    content: str


class BenchmarkLeanData(BaseModel):
    """Lean-specific parsed benchmark data.

    This extends ITPBenchmarkData with Lean-specific defaults and behavior.
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
    precond: str = "True -- default precond"
    postcond: str = ""
    proof: str = "sorry"

    @staticmethod
    def from_sections(sections: List[BenchmarkLeanDataSection]) -> "BenchmarkLeanData":
        """Build BenchmarkLeanData from a list of parsed sections."""
        lean_data = BenchmarkLeanData(
            task_imports="",
            solution_imports="",
            task_aux="",
            solution_aux="",
            code_aux="",
            precond_aux="",
            postcond_aux="",
            proof_aux="",
            code="",
            precond="True -- default precond",
            postcond="",
            proof="sorry",
        )

        for section in sections:
            if section.name == "import":
                if section.args.get("type") == "task":
                    lean_data.task_imports += f"\n{section.content}\n"
                elif section.args.get("type") == "solution":
                    lean_data.solution_imports += f"\n{section.content}\n"
            elif section.name in lean_data.model_fields:
                if section.content.strip():
                    setattr(lean_data, section.name, section.content)
            else:
                raise ValueError(f"Unknown section name: {section.name}")

        return lean_data

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


class LeanParser(ITPParser):
    """Lean-specific parser implementing ITPParser interface.

    Parses Lean source files with benchmark markers in the format:
    -- !benchmark @start section_name [args]
    ...content...
    -- !benchmark @end section_name
    """

    def get_comment_start_marker(self) -> str:
        """Return Lean single-line comment marker."""
        return "--"

    def get_comment_end_marker(self) -> str:
        """Lean uses single-line comments, so no end marker."""
        return ""

    def get_benchmark_marker(self) -> str:
        """Return the benchmark marker string."""
        return "!benchmark"

    def parse_benchmark_data(self, raw_content: str) -> ITPBenchmarkData:
        """Parse raw Lean source into benchmark data sections.

        Args:
            raw_content: Raw content of the Lean source file.

        Returns:
            Parsed ITPBenchmarkData with all sections extracted.
        """
        lean_data = parse_benchmark_lean_data(raw_content)
        return lean_data.to_itp_data()

    def parse_lean_data(self, raw_content: str) -> BenchmarkLeanData:
        """Parse raw Lean source into Lean-specific benchmark data.

        This method returns the Lean-specific data type for backward compatibility.

        Args:
            raw_content: Raw content of the Lean source file.

        Returns:
            Parsed BenchmarkLeanData with all sections extracted.
        """
        return parse_benchmark_lean_data(raw_content)


def parse_benchmark_lean_data(raw_lean_data: str) -> BenchmarkLeanData:
    """Parse Lean benchmark data from raw file content.

    This function parses Lean source files that use the benchmark marker format:
    -- !benchmark @start section_name [type=value]
    ...section content...
    -- !benchmark @end section_name

    Args:
        raw_lean_data: Raw content of the Lean file.

    Returns:
        Parsed BenchmarkLeanData with all sections extracted.
    """
    lines = raw_lean_data.strip().splitlines()
    sections = []

    current_section: Optional[BenchmarkLeanDataSection] = None

    for line in lines:
        if "-- !benchmark" not in line:
            if current_section is not None:
                current_section.content += line + "\n"
            continue

        line = line.split("-- !benchmark", 1)[1].strip()

        # Check for section start
        if line.startswith("@start"):
            parts = line.split("@start", 1)[1].strip().split(None, 1)
            section_name = parts[0].strip()

            if section_name in sections:
                raise ValueError(f"Duplicate section name: {section_name}")

            # Parse arguments if present
            args = {}
            if len(parts) > 1:
                arg_parts = parts[1].strip().split()
                for arg in arg_parts:
                    if "=" in arg:
                        key, value = arg.split("=", 1)
                        args[key] = value

            current_section = BenchmarkLeanDataSection(
                name=section_name, args=args, content=""
            )

        # Check for section end
        elif line.startswith("@end"):
            end_section = line.split("@end", 1)[1].strip()

            # Make sure we're ending the correct section
            if current_section and end_section == current_section.name:
                sections.append(current_section)
                current_section = None
            else:
                raise ValueError(
                    f"Unexpected end section: {end_section} for {current_section}. Currently nested sections are not supported."
                )

    return BenchmarkLeanData.from_sections(sections)


# Export public API
__all__ = [
    "LeanParser",
    "BenchmarkLeanData",
    "BenchmarkLeanDataSection",
    "parse_benchmark_lean_data",
]
