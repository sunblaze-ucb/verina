"""Dataset parsing module.

This module provides backward-compatible exports for benchmark data parsing.
The actual implementations are in the ITP-specific modules (lean/, coq/).

For new code, consider using:
    from verina.lean.parsing import LeanParser, BenchmarkLeanData
    from verina.coq.parsing import CoqParser, BenchmarkCoqData
"""

# Re-export from Lean parsing module for backward compatibility
from verina.lean.parsing import (
    BenchmarkLeanData,
    BenchmarkLeanDataSection,
    LeanParser,
    parse_benchmark_lean_data,
)

# Re-export ITP base classes
from verina.itp.base import ITPBenchmarkData, ITPBenchmarkDataSection

# Export public API - maintains backward compatibility
__all__ = [
    # Lean-specific (backward compatible)
    "BenchmarkLeanData",
    "BenchmarkLeanDataSection",
    "parse_benchmark_lean_data",
    "LeanParser",
    # ITP-generic
    "ITPBenchmarkData",
    "ITPBenchmarkDataSection",
]
