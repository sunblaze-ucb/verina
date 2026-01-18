#!/usr/bin/env python3
"""
Coq Watchdog Service:
1. Kills Coq processes (coqc, coqtop) running longer than timeout
2. Kills Coq processes exceeding memory limit (> 200GB default)
3. Warns on Coq processes exceeding warning limit (> 100GB default)
4. Periodic reporting of memory usage
5. Cleans up core dumps

Usage:
    python coq_watchdog.py <project_path> [options]

Options:
    --process-timeout   Seconds before killing Coq processes (default: 300)
    --memory-limit      GB of RAM before killing process (default: 200)
    --memory-warn       GB of RAM before warning (default: 100)
    --interval          Check interval in seconds (default: 5)
    --once              Run once and exit
"""

import argparse
import logging
import sys
import time
from pathlib import Path
from typing import Dict, Set, List

import psutil

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("coq_watchdog.log"),
    ],
)
logger = logging.getLogger(__name__)


class CoqWatchdog:
    def __init__(
        self,
        project_path: str,
        process_timeout: int = 300,
        memory_limit_gb: float = 200.0,
        memory_warn_gb: float = 100.0,
    ):
        self.project_path = Path(project_path)
        self.process_timeout = process_timeout
        
        self.memory_limit_gb = memory_limit_gb
        self.memory_limit_bytes = int(memory_limit_gb * (1024**3))
        
        self.memory_warn_gb = memory_warn_gb
        self.memory_warn_bytes = int(memory_warn_gb * (1024**3))

        # Process monitoring state
        self.monitored_processes: Dict[int, float] = {}
        self.killed_processes: Set[int] = set()

        # Stats
        self.processes_killed = 0
        self.files_deleted = 0

    # -------------------------------------------------------------------------
    # Process Monitoring
    # -------------------------------------------------------------------------

    def is_coq_process(self, process: psutil.Process) -> bool:
        """Check if a process is a Coq process (coqc, coqtop, etc)."""
        try:
            name = process.name().lower()
            
            # Skip Python processes (including this script)
            if "python" in name:
                return False

            cmdline = process.cmdline()
            # Skip self if run via python
            if cmdline and any("coq_watchdog.py" in arg for arg in cmdline):
                return False

            # Check for standard Coq binaries
            target_binaries = ["coqc", "coqtop", "coqide", "coq-tex", "coqdep"]
            
            # 1. Check simple process name
            if any(target in name for target in target_binaries):
                return True

            # 2. Check executable path/command line
            if cmdline:
                exe_name = cmdline[0].split("/")[-1].lower()
                if any(target in exe_name for target in target_binaries):
                    return True

            return False
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            return False

    def kill_process(self, process: psutil.Process, reason: str) -> bool:
        """Kill a process, trying SIGTERM then SIGKILL."""
        try:
            pid = process.pid
            try:
                age = time.time() - process.create_time()
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                age = 0.0
                
            logger.warning(f"Killing process {pid}: {reason} (age: {age:.1f}s)")

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
        """Check memory/timeout and log status."""
        current_time = time.time()
        current_pids = set()
        status_reports: List[str] = []

        attrs = ["pid", "name", "cmdline", "create_time", "memory_info"]
        
        for process in psutil.process_iter(attrs):
            try:
                if not self.is_coq_process(process):
                    continue

                pid = process.pid
                current_pids.add(pid)

                if pid in self.killed_processes:
                    continue

                # 1. Memory Check
                mem_info = process.info["memory_info"]
                rss_bytes = mem_info.rss if mem_info else 0
                rss_gb = rss_bytes / (1024**3)

                # Case A: Kill Limit (> 200GB)
                if rss_bytes > self.memory_limit_bytes:
                    reason = f"Memory Limit Exceeded ({rss_gb:.2f}GB > {self.memory_limit_gb}GB)"
                    if self.kill_process(process, reason):
                        self.killed_processes.add(pid)
                        self.processes_killed += 1
                    continue 

                # Case B: Warn Limit (> 100GB)
                if rss_bytes > self.memory_warn_bytes:
                    logger.warning(f"High Memory Warning: PID {pid} is using {rss_gb:.2f} GB")

                # 2. Timeout Check
                process_age = current_time - process.create_time()
                if process_age > self.process_timeout:
                    reason = f"Timeout Exceeded ({process_age:.1f}s > {self.process_timeout}s)"
                    if self.kill_process(process, reason):
                        self.killed_processes.add(pid)
                        self.processes_killed += 1
                    continue

                # 3. Track valid process
                if pid not in self.monitored_processes:
                    logger.debug(f"Monitoring Coq process {pid}")
                    self.monitored_processes[pid] = process.create_time()

                # Add to periodic summary report
                status_reports.append(f"{pid}({rss_gb:.1f}GB)")

            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        # Clean up finished processes from state
        finished = set(self.monitored_processes.keys()) - current_pids
        for pid in finished:
            del self.monitored_processes[pid]
            self.killed_processes.discard(pid)

        # Log periodic summary of active processes
        if status_reports:
            logger.info(f"Active Coq Processes: {', '.join(status_reports)}")

    # -------------------------------------------------------------------------
    # File Cleanup
    # -------------------------------------------------------------------------

    def cleanup_files(self):
        """Delete core dumps."""
        if not self.project_path.exists():
            return

        # Delete core dumps
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
        self.monitor_processes()
        self.cleanup_files()

    def run(self, interval: float = 5.0):
        logger.info(
            f"Starting Coq watchdog: path={self.project_path}, "
            f"timeout={self.process_timeout}s, "
            f"mem_kill={self.memory_limit_gb}GB, "
            f"mem_warn={self.memory_warn_gb}GB"
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
        description="Coq watchdog: kill hung/OOM coqc/coqtop processes"
    )
    parser.add_argument("project_path", help="Path to Coq project directory (for core dumps)")
    parser.add_argument(
        "-p", "--process-timeout",
        type=int,
        default=300,
        help="Kill Coq processes older than this (seconds, default: 300)",
    )
    parser.add_argument(
        "-m", "--memory-limit",
        type=float,
        default=200.0,
        help="Kill Coq processes using more than this RAM in GB (default: 200)",
    )
    parser.add_argument(
        "-w", "--memory-warn",
        type=float,
        default=100.0,
        help="Warn if Coq processes use more than this RAM in GB (default: 100)",
    )
    parser.add_argument(
        "-i", "--interval",
        type=float,
        default=5.0,
        help="Check interval in seconds (default: 5.0)",
    )
    parser.add_argument(
        "-1", "--once",
        action="store_true",
        help="Run once and exit",
    )

    args = parser.parse_args()
    watchdog = CoqWatchdog(
        args.project_path,
        process_timeout=args.process_timeout,
        memory_limit_gb=args.memory_limit,
        memory_warn_gb=args.memory_warn,
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