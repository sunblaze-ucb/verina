#!/usr/bin/env python3
"""
Combined Lean watchdog for:
1. Killing Lean/Lake processes running longer than timeout
2. Cleaning up stale temp files (*-*.lean pattern) older than max_age

Usage:
    python lean_watchdog.py <lean_project_path> [options]

Options:
    --process-timeout   Seconds before killing Lean processes (default: 80)
    --file-max-age      Seconds before deleting stale temp files (default: 130)
    --interval          Check interval in seconds (default: 5)
    --once              Run once and exit
"""

import argparse
import logging
import sys
import time
from pathlib import Path
from typing import Dict, Set

import psutil

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("lean_watchdog.log"),
    ],
)
logger = logging.getLogger(__name__)


class LeanWatchdog:
    def __init__(
        self,
        project_path: str,
        process_timeout: int = 80,
        file_max_age: int = 130,
    ):
        self.project_path = Path(project_path)
        self.process_timeout = process_timeout
        self.file_max_age = file_max_age

        # Process monitoring state
        self.monitored_processes: Dict[int, float] = {}
        self.killed_processes: Set[int] = set()

        # Stats
        self.processes_killed = 0
        self.files_deleted = 0

    # -------------------------------------------------------------------------
    # Process Monitoring
    # -------------------------------------------------------------------------

    def is_lean_process(self, process: psutil.Process) -> bool:
        """Check if a process is a lean/lake process (not Python)."""
        try:
            name = process.name().lower()

            # Skip Python processes
            if "python" in name:
                return False

            # Skip this script
            cmdline = process.cmdline()
            if cmdline and any("lean_watchdog.py" in arg for arg in cmdline):
                return False

            # Check process name
            if name.startswith("lean") or name.startswith("lake"):
                return True

            # Check executable name
            if cmdline:
                exe_name = cmdline[0].split("/")[-1].lower()
                if exe_name.startswith("lean") or exe_name.startswith("lake"):
                    return True

            return False
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            return False

    def kill_process(self, process: psutil.Process) -> bool:
        """Kill a process, trying SIGTERM then SIGKILL."""
        try:
            pid = process.pid
            age = time.time() - process.create_time()
            logger.warning(f"Killing lean process {pid} (running for {age:.1f}s)")

            process.terminate()
            try:
                process.wait(timeout=5)
                logger.info(f"Terminated process {pid}")
                return True
            except psutil.TimeoutExpired:
                logger.warning(f"Force killing process {pid}")
                process.kill()
                process.wait(timeout=5)
                logger.info(f"Killed process {pid}")
                return True
        except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
            logger.error(f"Failed to kill process: {e}")
            return False
        except Exception as e:
            logger.error(f"Unexpected error killing process: {e}")
            return False

    def monitor_processes(self):
        """Check and kill long-running Lean processes."""
        current_time = time.time()
        current_pids = set()

        for process in psutil.process_iter(["pid", "name", "cmdline", "create_time"]):
            try:
                if not self.is_lean_process(process):
                    continue

                pid = process.pid
                current_pids.add(pid)

                if pid in self.killed_processes:
                    continue

                process_age = current_time - process.create_time()
                if process_age > self.process_timeout:
                    if self.kill_process(process):
                        self.killed_processes.add(pid)
                        self.processes_killed += 1
                elif pid not in self.monitored_processes:
                    logger.debug(f"Monitoring lean process {pid}")
                    self.monitored_processes[pid] = process.create_time()

            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        # Clean up finished processes
        finished = set(self.monitored_processes.keys()) - current_pids
        for pid in finished:
            del self.monitored_processes[pid]
            self.killed_processes.discard(pid)

    # -------------------------------------------------------------------------
    # File Cleanup
    # -------------------------------------------------------------------------

    def is_temp_lean_file(self, filepath: Path) -> bool:
        """Check if file matches *-*.lean pattern (has hyphen in name)."""
        name = filepath.name
        return name.endswith(".lean") and "-" in name

    def is_core_dump(self, filepath: Path) -> bool:
        """Check if file is a core dump (core.*)."""
        return filepath.name.startswith("core.")

    def cleanup_files(self):
        """Delete stale temp Lean files and core dumps."""
        if not self.project_path.exists():
            return

        current_time = time.time()

        # Delete stale temp lean files
        for filepath in self.project_path.glob("*.lean"):
            if not self.is_temp_lean_file(filepath):
                continue

            try:
                file_age = current_time - filepath.stat().st_mtime
                if file_age > self.file_max_age:
                    logger.warning(
                        f"Deleting stale temp file: {filepath.name} (age: {file_age:.1f}s)"
                    )
                    filepath.unlink()
                    self.files_deleted += 1
            except (OSError, FileNotFoundError):
                pass

        # Delete core dumps immediately (no age check)
        for filepath in self.project_path.glob("core.*"):
            try:
                size_mb = filepath.stat().st_size / (1024 * 1024)
                logger.warning(f"Deleting core dump: {filepath.name} ({size_mb:.1f}MB)")
                filepath.unlink()
                self.files_deleted += 1
            except (OSError, FileNotFoundError):
                pass

    # -------------------------------------------------------------------------
    # Main Loop
    # -------------------------------------------------------------------------

    def run_once(self):
        """Run one monitoring cycle."""
        self.monitor_processes()
        self.cleanup_files()

    def run(self, interval: float = 5.0):
        """Run continuously."""
        logger.info(
            f"Starting Lean watchdog: path={self.project_path}, "
            f"process_timeout={self.process_timeout}s, "
            f"file_max_age={self.file_max_age}s, interval={interval}s"
        )
        try:
            while True:
                self.run_once()
                time.sleep(interval)
        except KeyboardInterrupt:
            logger.info(
                f"Stopped. Killed {self.processes_killed} processes, "
                f"deleted {self.files_deleted} files."
            )


def main():
    parser = argparse.ArgumentParser(
        description="Lean watchdog: kill hung processes and clean stale temp files"
    )
    parser.add_argument("project_path", help="Path to Lean project directory")
    parser.add_argument(
        "-p", "--process-timeout",
        type=int,
        default=80,
        help="Kill Lean processes older than this (seconds, default: 80)",
    )
    parser.add_argument(
        "-f", "--file-max-age",
        type=int,
        default=130,
        help="Delete temp files older than this (seconds, default: 130)",
    )
    parser.add_argument(
        "-i", "--interval",
        type=float,
        default=1.0,
        help="Check interval in seconds (default: 1)",
    )
    parser.add_argument(
        "-1", "--once",
        action="store_true",
        help="Run once and exit",
    )

    args = parser.parse_args()
    watchdog = LeanWatchdog(
        args.project_path,
        process_timeout=args.process_timeout,
        file_max_age=args.file_max_age,
    )

    if args.once:
        logger.info("Running single check...")
        watchdog.run_once()
        logger.info(
            f"Done. Killed {watchdog.processes_killed} processes, "
            f"deleted {watchdog.files_deleted} files."
        )
    else:
        watchdog.run(args.interval)


if __name__ == "__main__":
    main()
