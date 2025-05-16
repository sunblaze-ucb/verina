from datetime import datetime
from pathlib import Path
from typing import Optional

from loguru import logger

from llm4verification.utils.path import ROOT_DIR


def enable_file_logger(
    log_dir: Optional[Path] = None, log_file: Optional[str] = None
) -> None:
    if log_dir is None:
        log_dir = ROOT_DIR / "logs"

    if log_file is None:
        # Use current time as the log file name
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_file = f"{timestamp}.log"

    log_dir.mkdir(parents=True, exist_ok=True)
    logger.add(log_dir / log_file, rotation="10 MB", compression="zip")
