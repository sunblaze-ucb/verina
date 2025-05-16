import asyncio
import shutil
import subprocess
from pathlib import Path
from typing import Optional, Tuple

from loguru import logger

from llm4verification.utils import ROOT_DIR

LEAN_WORKING_DIR = ROOT_DIR
LEAN_PLAYGROUND_DIR = LEAN_WORKING_DIR / "lean-playground"


def create_lean_file(file_name: str, content: str) -> Path:
    """
    Create a Lean file with the given content.

    Args:
        file_name: Name of the Lean file.
        content: Content of the Lean file.

    Returns:
        path: Path to the created Lean file.
    """
    lean_file = LEAN_PLAYGROUND_DIR / f"{file_name}.lean"
    with open(lean_file, "w") as f:
        f.write(content)
    return lean_file


def copy_lean_file(lean_file: Path, new_file_name: Optional[str] = None) -> Path:
    """
    Copy a Lean file to the Lean playground directory.

    Args:
        lean_file: Path to the Lean file.
        new_file_name: Optional new name for the copied file.

    Returns:
        path: Path to the copied Lean file.
    """
    if new_file_name is None:
        new_file_name = lean_file.stem
    new_lean_file = LEAN_PLAYGROUND_DIR / f"{new_file_name}.lean"
    shutil.copy(lean_file, new_lean_file)
    return new_lean_file


def clean_playground() -> None:
    """
    Clean the Lean playground directory.
    """
    for file in LEAN_PLAYGROUND_DIR.iterdir():
        if file.name != ".gitkeep":
            if file.is_dir():
                shutil.rmtree(file)
            else:
                file.unlink()


# bug: cannot kill timeout process, use sync version
async def check_lean_compile_async(
    lean_file: Path, timeout: int = 180
) -> Tuple[bool, str]:
    """
    Check if the Lean file can be compiled.

    Args:
        lean_file: Path to the Lean file.

    Returns:
        bool: Whether the Lean file can be compiled.
    """
    proc = None
    try:
        async with asyncio.timeout(timeout):
            proc = await asyncio.create_subprocess_exec(
                "lake",
                "lean",
                str(lean_file),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=LEAN_WORKING_DIR,
            )
            stdout, stderr = await proc.communicate()
            returncode = proc.returncode
            if returncode == 0:
                return True, stdout.decode()
            else:
                # logger.error(f"Lean compilation failed for {lean_file}")
                # logger.error(f"stdout: {stdout.decode()}")
                # logger.error(f"stderr: {stderr.decode()}")
                return False, stdout.decode()
    except TimeoutError:
        if proc is not None:
            proc.kill()
            try:
                await asyncio.wait_for(proc.wait(), timeout=5)
            except TimeoutError:
                logger.warning(
                    f"Failed to kill Lean process for {lean_file}, forgetting it."
                )
        logger.warning(f"Lean compilation timed out after {timeout}s for {lean_file}")
        return False, "TIMEOUT"
    except Exception as e:
        logger.error(f"Error during Lean compilation for {lean_file}: {e}")
        return False, "COMPERROR: " + str(e)


def check_lean_compile(lean_file: Path, timeout: int = 120) -> Tuple[bool, str]:
    """
    Check if the Lean file can be compiled.
    Note: This function requires `timeout` command to be available in the system.

    Args:
        lean_file: Path to the Lean file.

    Returns:
        bool: Whether the Lean file can be compiled.
    """
    try:
        # Add 30 second timeout to prevent hanging
        result = subprocess.run(
            # ["timeout", str(timeout + 10), "lake", "lean", str(lean_file)],
            ["lake", "lean", str(lean_file)],
            check=False,  # Don't raise exception, we'll handle the return code
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            cwd=LEAN_WORKING_DIR,
        )

        if result.returncode != 0:
            # logger.warning(f"Lean compilation failed for {lean_file}")
            # logger.warning(f"stdout: {result.stdout.decode()}")
            # logger.warning(f"stderr: {result.stderr.decode()}")
            if result.returncode == 124:
                logger.warning(
                    f"Lean compilation timed out after {timeout}s for {lean_file}"
                )
                return False, "TIMEOUT"
            return False, result.stdout.decode() + "\n" + result.stderr.decode()

        return True, result.stdout.decode() + "\n" + result.stderr.decode()

    except subprocess.TimeoutExpired:
        logger.warning(f"Lean compilation timed out after {timeout}s for {lean_file}")
        return False, "TIMEOUT"
    except Exception as e:
        logger.error(f"Error during Lean compilation for {lean_file}: {e}")
        return False, "COMPERROR: " + str(e)


if __name__ == "__main__":

    async def main():
        # Example usage
        clean_playground()
        lean_file = create_lean_file("example", " example : 1 != 1 := by simp")
        can_compile, output = await check_lean_compile_async(lean_file)
        if can_compile:
            logger.info(f"{lean_file} compiled successfully.")
            logger.info(f"Output: {output}")
        else:
            logger.error(f"{lean_file} failed to compile.")
            logger.error(f"Output: {output}")

    asyncio.run(main())
