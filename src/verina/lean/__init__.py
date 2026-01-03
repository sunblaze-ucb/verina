"""Lean 4 theorem prover integration for Verina benchmark.

This module provides the Lean-specific implementation of the ITP interface,
including compilation, parsing, and template rendering.
"""

import asyncio
import shutil
import subprocess
from pathlib import Path
from typing import Optional, Tuple

from loguru import logger

from verina.itp import ITPType, register_itp
from verina.itp.base import ITPCompiler
from verina.utils import ROOT_DIR

LEAN_WORKING_DIR = ROOT_DIR
LEAN_PLAYGROUND_DIR = LEAN_WORKING_DIR / "lean-playground"


class LeanCompiler(ITPCompiler):
    """Lean 4 compiler implementation of ITPCompiler interface."""

    def get_name(self) -> str:
        return "lean"

    def get_working_dir(self) -> Path:
        return LEAN_WORKING_DIR

    def get_playground_dir(self) -> Path:
        return LEAN_PLAYGROUND_DIR

    def create_source_file(self, file_name: str, content: str) -> Path:
        """Create a Lean file with the given content.

        Args:
            file_name: Name of the Lean file (without extension).
            content: Content of the Lean file.

        Returns:
            Path to the created Lean file.
        """
        lean_file = LEAN_PLAYGROUND_DIR / f"{file_name}.lean"
        with open(lean_file, "w") as f:
            f.write(content)
        return lean_file

    def check_compile(self, source_file: Path, timeout: int = 120) -> Tuple[bool, str]:
        """Check if the Lean file can be compiled.

        Args:
            source_file: Path to the Lean file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        try:
            result = subprocess.run(
                ["lake", "lean", str(source_file)],
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                cwd=LEAN_WORKING_DIR,
            )

            if result.returncode != 0:
                if result.returncode == 124:
                    logger.warning(
                        f"Lean compilation timed out after {timeout}s for {source_file}"
                    )
                    return False, "TIMEOUT"
                return False, result.stdout.decode() + "\n" + result.stderr.decode()

            return True, result.stdout.decode() + "\n" + result.stderr.decode()

        except subprocess.TimeoutExpired:
            logger.warning(f"Lean compilation timed out after {timeout}s for {source_file}")
            return False, "TIMEOUT"
        except Exception as e:
            logger.error(f"Error during Lean compilation for {source_file}: {e}")
            return False, "COMPERROR: " + str(e)

    async def check_compile_async(self, source_file: Path, timeout: int = 180) -> Tuple[bool, str]:
        """Async version of check_compile.

        Note: There's a known bug where timeout processes can't be killed properly,
        so the sync version is preferred.

        Args:
            source_file: Path to the Lean file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        proc = None
        try:
            async with asyncio.timeout(timeout):
                proc = await asyncio.create_subprocess_exec(
                    "lake",
                    "lean",
                    str(source_file),
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    cwd=LEAN_WORKING_DIR,
                )
                stdout, stderr = await proc.communicate()
                returncode = proc.returncode
                if returncode == 0:
                    return True, stdout.decode()
                else:
                    return False, stdout.decode()
        except TimeoutError:
            if proc is not None:
                proc.kill()
                try:
                    await asyncio.wait_for(proc.wait(), timeout=5)
                except TimeoutError:
                    logger.warning(
                        f"Failed to kill Lean process for {source_file}, forgetting it."
                    )
            logger.warning(f"Lean compilation timed out after {timeout}s for {source_file}")
            return False, "TIMEOUT"
        except Exception as e:
            logger.error(f"Error during Lean compilation for {source_file}: {e}")
            return False, "COMPERROR: " + str(e)

    def clean_playground(self) -> None:
        """Clean the Lean playground directory."""
        for file in LEAN_PLAYGROUND_DIR.iterdir():
            if file.name != ".gitkeep":
                if file.is_dir():
                    shutil.rmtree(file)
                else:
                    file.unlink()

    def get_file_extension(self) -> str:
        return ".lean"

    def copy_source_file(self, source_file: Path, new_file_name: Optional[str] = None) -> Path:
        """Copy a Lean file to the Lean playground directory.

        Args:
            source_file: Path to the Lean file.
            new_file_name: Optional new name for the copied file.

        Returns:
            Path to the copied Lean file.
        """
        if new_file_name is None:
            new_file_name = source_file.stem
        new_lean_file = LEAN_PLAYGROUND_DIR / f"{new_file_name}.lean"
        shutil.copy(source_file, new_lean_file)
        return new_lean_file


# =============================================================================
# Backward compatibility: Keep existing standalone functions
# =============================================================================

def create_lean_file(file_name: str, content: str) -> Path:
    """Create a Lean file with the given content.

    Args:
        file_name: Name of the Lean file.
        content: Content of the Lean file.

    Returns:
        path: Path to the created Lean file.
    """
    return LeanCompiler().create_source_file(file_name, content)


def copy_lean_file(lean_file: Path, new_file_name: Optional[str] = None) -> Path:
    """Copy a Lean file to the Lean playground directory.

    Args:
        lean_file: Path to the Lean file.
        new_file_name: Optional new name for the copied file.

    Returns:
        path: Path to the copied Lean file.
    """
    return LeanCompiler().copy_source_file(lean_file, new_file_name)


def clean_playground() -> None:
    """Clean the Lean playground directory."""
    LeanCompiler().clean_playground()


async def check_lean_compile_async(
    lean_file: Path, timeout: int = 180
) -> Tuple[bool, str]:
    """Check if the Lean file can be compiled (async version).

    Args:
        lean_file: Path to the Lean file.
        timeout: Timeout in seconds.

    Returns:
        Tuple of (success, output/error message).
    """
    return await LeanCompiler().check_compile_async(lean_file, timeout)


def check_lean_compile(lean_file: Path, timeout: int = 120) -> Tuple[bool, str]:
    """Check if the Lean file can be compiled.

    Args:
        lean_file: Path to the Lean file.
        timeout: Timeout in seconds.

    Returns:
        Tuple of (success, output/error message).
    """
    return LeanCompiler().check_compile(lean_file, timeout)


# =============================================================================
# Registration and exports
# =============================================================================

# Import parsing and template modules (these will be created)
# They need to be imported after the module is set up to avoid circular imports
def _register_lean():
    """Register Lean as an ITP implementation."""
    from verina.lean.parsing import LeanParser
    from verina.lean.template import LeanGenerationTaskTemplate

    register_itp(
        ITPType.LEAN,
        compiler_class=LeanCompiler,
        parser_class=LeanParser,
        template_class=LeanGenerationTaskTemplate,
    )


# Export public API
__all__ = [
    # Class
    "LeanCompiler",
    # Legacy functions (backward compatible)
    "create_lean_file",
    "copy_lean_file",
    "clean_playground",
    "check_lean_compile",
    "check_lean_compile_async",
    # Constants
    "LEAN_WORKING_DIR",
    "LEAN_PLAYGROUND_DIR",
]


if __name__ == "__main__":

    async def main():
        # Example usage
        compiler = LeanCompiler()
        compiler.clean_playground()
        lean_file = compiler.create_source_file("example", " example : 1 != 1 := by simp")
        can_compile, output = await compiler.check_compile_async(lean_file)
        if can_compile:
            logger.info(f"{lean_file} compiled successfully.")
            logger.info(f"Output: {output}")
        else:
            logger.error(f"{lean_file} failed to compile.")
            logger.error(f"Output: {output}")

    asyncio.run(main())
