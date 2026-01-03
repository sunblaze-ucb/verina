"""Coq/Rocq theorem prover integration for Verina benchmark.

This module provides the Coq-specific implementation of the ITP interface,
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

COQ_WORKING_DIR = ROOT_DIR
COQ_PLAYGROUND_DIR = COQ_WORKING_DIR / "coq-playground"


class CoqCompiler(ITPCompiler):
    """Coq compiler implementation of ITPCompiler interface.

    Uses coqc for compilation, similar to how Lean uses 'lake lean'.
    Supports Docker execution for QuickChick integration.
    """

    def __init__(self, docker_image: Optional[str] = None):
        """Initialize CoqCompiler.

        Args:
            docker_image: Docker image to use for compilation (e.g., 'verina-coq').
                         If None, uses local coqc installation.
        """
        self.docker_image = docker_image

    def get_name(self) -> str:
        return "coq"

    def get_working_dir(self) -> Path:
        return COQ_WORKING_DIR

    def get_playground_dir(self) -> Path:
        return COQ_PLAYGROUND_DIR

    def _get_compile_command(self, source_file: Path) -> list:
        """Get the compilation command (local or Docker).

        Args:
            source_file: Path to the Coq file.

        Returns:
            List of command arguments.
        """
        if self.docker_image:
            # Use Docker with volume mount
            # Mount the playground directory to /workspace
            return [
                "docker", "run", "--rm",
                "-v", f"{COQ_PLAYGROUND_DIR}:/workspace",
                self.docker_image,
                "coqc",
                f"/workspace/{source_file.name}"
            ]
        else:
            # Use local coqc
            return [
                "coqc",
                "-Q", str(COQ_PLAYGROUND_DIR), "Playground",
                str(source_file)
            ]

    def create_source_file(self, file_name: str, content: str) -> Path:
        """Create a Coq file with the given content.

        Args:
            file_name: Name of the Coq file (without extension).
            content: Content of the Coq file.

        Returns:
            Path to the created Coq file.
        """
        # Ensure playground directory exists
        COQ_PLAYGROUND_DIR.mkdir(parents=True, exist_ok=True)

        # Sanitize file name - Coq doesn't like dashes in identifiers
        # and identifiers cannot start with a digit
        safe_file_name = file_name.replace("-", "_")
        if safe_file_name and safe_file_name[0].isdigit():
            safe_file_name = "f_" + safe_file_name
        coq_file = COQ_PLAYGROUND_DIR / f"{safe_file_name}.v"
        with open(coq_file, "w") as f:
            f.write(content)
        return coq_file

    def check_compile(self, source_file: Path, timeout: int = 120) -> Tuple[bool, str]:
        """Check if the Coq file can be compiled.

        Args:
            source_file: Path to the Coq file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        try:
            cmd = self._get_compile_command(source_file)
            result = subprocess.run(
                cmd,
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                cwd=COQ_WORKING_DIR,
            )

            if result.returncode != 0:
                if result.returncode == 124:
                    logger.warning(
                        f"Coq compilation timed out after {timeout}s for {source_file}"
                    )
                    return False, "TIMEOUT"
                return False, result.stdout.decode() + "\n" + result.stderr.decode()

            return True, result.stdout.decode() + "\n" + result.stderr.decode()

        except subprocess.TimeoutExpired:
            logger.warning(f"Coq compilation timed out after {timeout}s for {source_file}")
            return False, "TIMEOUT"
        except FileNotFoundError as e:
            if self.docker_image:
                logger.error("docker not found. Please install Docker.")
                return False, "COMPERROR: docker not found"
            else:
                logger.error("coqc not found. Please install Coq: opam install rocq-core")
                return False, "COMPERROR: coqc not found"
        except Exception as e:
            logger.error(f"Error during Coq compilation for {source_file}: {e}")
            return False, "COMPERROR: " + str(e)

    async def check_compile_async(self, source_file: Path, timeout: int = 180) -> Tuple[bool, str]:
        """Async version of check_compile.

        Args:
            source_file: Path to the Coq file.
            timeout: Timeout in seconds.

        Returns:
            Tuple of (success, output/error message).
        """
        proc = None
        try:
            cmd = self._get_compile_command(source_file)
            async with asyncio.timeout(timeout):
                proc = await asyncio.create_subprocess_exec(
                    *cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    cwd=COQ_WORKING_DIR,
                )
                stdout, stderr = await proc.communicate()
                returncode = proc.returncode
                if returncode == 0:
                    return True, stdout.decode()
                else:
                    return False, stdout.decode() + "\n" + stderr.decode()
        except TimeoutError:
            if proc is not None:
                proc.kill()
                try:
                    await asyncio.wait_for(proc.wait(), timeout=5)
                except TimeoutError:
                    logger.warning(
                        f"Failed to kill Coq process for {source_file}, forgetting it."
                    )
            logger.warning(f"Coq compilation timed out after {timeout}s for {source_file}")
            return False, "TIMEOUT"
        except FileNotFoundError as e:
            if self.docker_image:
                logger.error("docker not found. Please install Docker.")
                return False, "COMPERROR: docker not found"
            else:
                logger.error("coqc not found. Please install Coq: opam install rocq-core")
                return False, "COMPERROR: coqc not found"
        except Exception as e:
            logger.error(f"Error during Coq compilation for {source_file}: {e}")
            return False, "COMPERROR: " + str(e)

    def clean_playground(self) -> None:
        """Clean the Coq playground directory."""
        if not COQ_PLAYGROUND_DIR.exists():
            return

        for file in COQ_PLAYGROUND_DIR.iterdir():
            if file.name not in (".gitkeep", "_CoqProject"):
                if file.is_dir():
                    shutil.rmtree(file)
                else:
                    file.unlink()

    def get_file_extension(self) -> str:
        return ".v"

    def copy_source_file(self, source_file: Path, new_file_name: Optional[str] = None) -> Path:
        """Copy a Coq file to the Coq playground directory.

        Args:
            source_file: Path to the Coq file.
            new_file_name: Optional new name for the copied file.

        Returns:
            Path to the copied Coq file.
        """
        # Ensure playground directory exists
        COQ_PLAYGROUND_DIR.mkdir(parents=True, exist_ok=True)

        if new_file_name is None:
            new_file_name = source_file.stem
        new_coq_file = COQ_PLAYGROUND_DIR / f"{new_file_name}.v"
        shutil.copy(source_file, new_coq_file)
        return new_coq_file


# =============================================================================
# Convenience functions (similar to Lean module)
# =============================================================================

def create_coq_file(file_name: str, content: str) -> Path:
    """Create a Coq file with the given content.

    Args:
        file_name: Name of the Coq file.
        content: Content of the Coq file.

    Returns:
        path: Path to the created Coq file.
    """
    return CoqCompiler().create_source_file(file_name, content)


def copy_coq_file(coq_file: Path, new_file_name: Optional[str] = None) -> Path:
    """Copy a Coq file to the Coq playground directory.

    Args:
        coq_file: Path to the Coq file.
        new_file_name: Optional new name for the copied file.

    Returns:
        path: Path to the copied Coq file.
    """
    return CoqCompiler().copy_source_file(coq_file, new_file_name)


def clean_coq_playground() -> None:
    """Clean the Coq playground directory."""
    CoqCompiler().clean_playground()


async def check_coq_compile_async(
    coq_file: Path, timeout: int = 180
) -> Tuple[bool, str]:
    """Check if the Coq file can be compiled (async version).

    Args:
        coq_file: Path to the Coq file.
        timeout: Timeout in seconds.

    Returns:
        Tuple of (success, output/error message).
    """
    return await CoqCompiler().check_compile_async(coq_file, timeout)


def check_coq_compile(coq_file: Path, timeout: int = 120) -> Tuple[bool, str]:
    """Check if the Coq file can be compiled.

    Args:
        coq_file: Path to the Coq file.
        timeout: Timeout in seconds.

    Returns:
        Tuple of (success, output/error message).
    """
    return CoqCompiler().check_compile(coq_file, timeout)


# =============================================================================
# Registration and exports
# =============================================================================

def _register_coq():
    """Register Coq as an ITP implementation."""
    from verina.coq.parsing import CoqParser
    from verina.coq.template import CoqGenerationTaskTemplate

    register_itp(
        ITPType.COQ,
        compiler_class=CoqCompiler,
        parser_class=CoqParser,
        template_class=CoqGenerationTaskTemplate,
    )


# Export public API
__all__ = [
    # Class
    "CoqCompiler",
    # Convenience functions
    "create_coq_file",
    "copy_coq_file",
    "clean_coq_playground",
    "check_coq_compile",
    "check_coq_compile_async",
    # Constants
    "COQ_WORKING_DIR",
    "COQ_PLAYGROUND_DIR",
]


if __name__ == "__main__":

    async def main():
        # Example usage
        compiler = CoqCompiler()
        compiler.clean_playground()
        coq_file = compiler.create_source_file(
            "example",
            "Lemma test : 1 = 1. Proof. reflexivity. Qed."
        )
        can_compile, output = await compiler.check_compile_async(coq_file)
        if can_compile:
            logger.info(f"{coq_file} compiled successfully.")
            logger.info(f"Output: {output}")
        else:
            logger.error(f"{coq_file} failed to compile.")
            logger.error(f"Output: {output}")

    asyncio.run(main())
