from typing import Dict, List, Optional

from pydantic import BaseModel


class BenchmarkLeanDataSection(BaseModel):
    name: str
    args: Dict[str, str]
    content: str


class BenchmarkLeanData(BaseModel):
    task_imports: str
    solution_imports: str

    task_aux: str
    solution_aux: str
    code_aux: str
    precond_aux: str
    postcond_aux: str
    proof_aux: str

    code: str
    precond: str
    postcond: str
    proof: str

    @staticmethod
    def from_sections(sections: List[BenchmarkLeanDataSection]) -> "BenchmarkLeanData":
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


def parse_benchmark_lean_data(raw_lean_data: str) -> BenchmarkLeanData:
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
