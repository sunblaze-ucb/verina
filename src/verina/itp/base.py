"""Abstract base classes for ITP (Interactive Theorem Prover) interfaces.

This module defines the abstract interfaces that both Lean and Coq implementations must follow,
enabling a unified API for the benchmark framework.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from pydantic import BaseModel


class ITPBenchmarkDataSection(BaseModel):
    """A section of ITP benchmark data with name, args, and content."""
    name: str
    args: Dict[str, str]
    content: str


class ITPBenchmarkData(BaseModel):
    """ITP-agnostic parsed benchmark data.

    This represents the parsed sections from an ITP source file,
    independent of whether it's Lean or Coq.
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
    proof: str = ""  # default: incomplete proof

    @staticmethod
    def from_sections(sections: List[ITPBenchmarkDataSection]) -> "ITPBenchmarkData":
        """Build ITPBenchmarkData from a list of parsed sections."""
        data = ITPBenchmarkData()

        for section in sections:
            if section.name == "import":
                if section.args.get("type") == "task":
                    data.task_imports += f"\n{section.content}\n"
                elif section.args.get("type") == "solution":
                    data.solution_imports += f"\n{section.content}\n"
            elif section.name in data.model_fields:
                if section.content.strip():
                    setattr(data, section.name, section.content)
            else:
                raise ValueError(f"Unknown section name: {section.name}")

        return data


class ITPCompiler(ABC):
    """Abstract interface for ITP compilation.

    Implementations handle creating source files and checking compilation
    for a specific theorem prover (Lean, Coq, etc.).
    """

    @abstractmethod
    def get_name(self) -> str:
        """Return the ITP name (e.g., 'lean', 'coq')."""
        pass

    @abstractmethod
    def get_working_dir(self) -> Path:
        """Return the working directory for compilation."""
        pass

    @abstractmethod
    def get_playground_dir(self) -> Path:
        """Return the playground directory for temporary files."""
        pass

    @abstractmethod
    def create_source_file(self, file_name: str, content: str) -> Path:
        """Create a source file in the playground.

        Args:
            file_name: Name of the file (without extension).
            content: Content of the source file.

        Returns:
            Path to the created source file.
        """
        pass

    @abstractmethod
    def check_compile(self, source_file: Path, timeout: int = 120) -> Tuple[bool, str]:
        """Compile the source file and return result.

        Args:
            source_file: Path to the source file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        pass

    @abstractmethod
    def check_compile_async(self, source_file: Path, timeout: int = 180) -> Tuple[bool, str]:
        """Async version of check_compile.

        Args:
            source_file: Path to the source file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        pass

    @abstractmethod
    def clean_playground(self) -> None:
        """Clean temporary files from the playground directory."""
        pass

    @abstractmethod
    def get_file_extension(self) -> str:
        """Return the file extension for this ITP (e.g., '.lean', '.v')."""
        pass

    @abstractmethod
    def copy_source_file(self, source_file: Path, new_file_name: Optional[str] = None) -> Path:
        """Copy a source file to the playground.

        Args:
            source_file: Path to the source file to copy.
            new_file_name: Optional new name for the copied file.

        Returns:
            Path to the copied file.
        """
        pass


class ITPParser(ABC):
    """Abstract interface for parsing ITP source files.

    Implementations handle parsing benchmark markers from ITP-specific
    source files (Lean uses --, Coq uses (* *)).
    """

    @abstractmethod
    def get_comment_start_marker(self) -> str:
        """Return comment start pattern (e.g., '--' for Lean, '(*' for Coq)."""
        pass

    @abstractmethod
    def get_comment_end_marker(self) -> str:
        """Return comment end pattern (e.g., '' for Lean single-line, '*)' for Coq)."""
        pass

    @abstractmethod
    def get_benchmark_marker(self) -> str:
        """Return the benchmark marker string (e.g., '!benchmark')."""
        pass

    @abstractmethod
    def parse_benchmark_data(self, raw_content: str) -> ITPBenchmarkData:
        """Parse raw ITP source into benchmark data sections.

        Args:
            raw_content: Raw content of the ITP source file.

        Returns:
            Parsed ITPBenchmarkData with all sections extracted.
        """
        pass


class ITPTemplate(ABC):
    """Abstract interface for rendering ITP code.

    Implementations handle rendering code, specs, proofs, and tests
    in the syntax of a specific theorem prover.
    """

    # Test message markers - implementations should override these
    CODE_TEST_MSG_MARKER: str = "code_test"
    PRECOND_TEST_DECIDABLE_MSG_MARKER: str = "precond_test_decidable"
    POSTCOND_TEST_DECIDABLE_MSG_MARKER: str = "postcond_test_decidable"

    @abstractmethod
    def get_name(self) -> str:
        """Return the ITP name (e.g., 'lean', 'coq')."""
        pass

    @abstractmethod
    def render_imports(self, imports: str, type_: str) -> str:
        """Render import section with benchmark markers.

        Args:
            imports: Import statements.
            type_: Import type (e.g., 'task', 'solution').
        """
        pass

    @abstractmethod
    def render_aux(self, aux: str, type_: str) -> str:
        """Render auxiliary section with benchmark markers.

        Args:
            aux: Auxiliary code.
            type_: Aux type (e.g., 'code', 'precond', 'postcond', 'proof').
        """
        pass

    @abstractmethod
    def render_test_imports(self) -> str:
        """Render imports needed for testing (e.g., Plausible, QuickChick)."""
        pass

    @abstractmethod
    def render_param_list(self) -> str:
        """Render function parameter list in ITP syntax."""
        pass

    @abstractmethod
    def render_precond(self, precond: str, *, precond_name: str = "") -> str:
        """Render precondition definition.

        Args:
            precond: Precondition body.
            precond_name: Optional name suffix for the precondition.
        """
        pass

    @abstractmethod
    def render_code(self, code: str, *, precond_name: str = "") -> str:
        """Render code/function definition.

        Args:
            code: Function body.
            precond_name: Optional name suffix for the precondition reference.
        """
        pass

    @abstractmethod
    def render_postcond(self, postcond: str, *, precond_name: str = "", postcond_name: str = "") -> str:
        """Render postcondition definition.

        Args:
            postcond: Postcondition body.
            precond_name: Optional name suffix for the precondition reference.
            postcond_name: Optional name suffix for the postcondition.
        """
        pass

    @abstractmethod
    def render_proof(self, proof: str, *, precond_name: str = "", postcond_name: str = "") -> str:
        """Render proof/theorem.

        Args:
            proof: Proof body/tactics.
            precond_name: Optional name suffix for the precondition reference.
            postcond_name: Optional name suffix for the postcondition reference.
        """
        pass

    @abstractmethod
    def render_unit_test_value(self, itp_type: str, value: Any) -> str:
        """Render a value literal in ITP syntax.

        Args:
            itp_type: The ITP type of the value.
            value: The value to render.
        """
        pass

    @abstractmethod
    def render_code_unit_test(self, test_case: Any, *, test_idx: int) -> str:
        """Render a unit test for code.

        Args:
            test_case: TestCase with input and expected output.
            test_idx: Index of this test case.
        """
        pass

    @abstractmethod
    def get_decidable_err_msg(self) -> str:
        """Return the error message indicating decidability failure."""
        pass

    @abstractmethod
    def get_decidable_unknown_msg(self) -> str:
        """Return the message indicating decidability is unknown."""
        pass

    @abstractmethod
    def get_pbt_success_msg(self) -> str:
        """Return property-based testing success message (plausible/quickchick)."""
        pass

    @abstractmethod
    def get_pbt_failed_msg(self) -> str:
        """Return property-based testing failure message."""
        pass

    @abstractmethod
    def get_pbt_gave_up_msg(self) -> str:
        """Return property-based testing gave up message."""
        pass

    @abstractmethod
    def get_pbt_test_command(self) -> str:
        """Return the property-based testing command/tactic."""
        pass

    @abstractmethod
    def get_cheat_codes(self) -> List[str]:
        """Return list of cheat codes that invalidate proofs (e.g., 'sorry', 'admit')."""
        pass

    @staticmethod
    @abstractmethod
    def PRECOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        """Return marker for undecidable precondition test of given type."""
        pass

    @staticmethod
    @abstractmethod
    def POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        """Return marker for undecidable postcondition test of given type."""
        pass
