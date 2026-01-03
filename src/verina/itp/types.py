"""Common type utilities for ITP abstraction layer.

This module provides type-related utilities that are shared across
different ITP implementations.
"""

from enum import Enum
from typing import Any, Dict, List, Optional

from pydantic import BaseModel


class TestScore(str, Enum):
    """Generic test score across ITPs."""
    PASS = "pass"
    FAIL = "fail"
    UNKNOWN = "unknown"


class SpecFormalScore(BaseModel):
    """Formal verification score for specifications."""
    sound: TestScore = TestScore.UNKNOWN
    complete: TestScore = TestScore.UNKNOWN


class SpecTestScoreDetail(BaseModel):
    """Detailed test score for specification tests."""
    decide: TestScore = TestScore.UNKNOWN
    pbt: TestScore = TestScore.UNKNOWN  # Property-based testing (plausible/quickchick)
    pbt_inverse: TestScore = TestScore.UNKNOWN
    llm: TestScore = TestScore.UNKNOWN
    llm_inverse: TestScore = TestScore.UNKNOWN

    def to_score(self) -> TestScore:
        """Convert detailed scores to a single score."""
        if self.decide != TestScore.UNKNOWN:
            return self.decide
        if TestScore.FAIL in [self.pbt, self.pbt_inverse]:
            return TestScore.FAIL
        if TestScore.PASS in [self.pbt, self.pbt_inverse]:
            return TestScore.PASS
        assert self.llm != TestScore.FAIL, f"LLM score should not be FAIL: {self.llm}"
        assert self.llm_inverse != TestScore.FAIL, f"LLM inverse score should not be FAIL: {self.llm_inverse}"
        if TestScore.PASS in [self.llm, self.llm_inverse]:
            return TestScore.PASS
        return TestScore.UNKNOWN


class SpecTestScore(BaseModel):
    """Test score with detailed breakdown."""
    score: TestScore = TestScore.UNKNOWN
    score_detail: SpecTestScoreDetail = SpecTestScoreDetail()

    def update_score(self):
        """Update aggregate score from detail."""
        self.score = self.score_detail.to_score()


class TestsSummary(BaseModel):
    """Summary of test results."""
    score: TestScore = TestScore.UNKNOWN
    pass_count: int = 0
    fail_count: int = 0
    unknown_count: int = 0

    def update_score(self):
        """Update aggregate score from counts."""
        if self.fail_count > 0:
            self.score = TestScore.FAIL
        elif self.unknown_count > 0:
            self.score = TestScore.UNKNOWN
        else:
            self.score = TestScore.PASS  # all tests passed or no tests


# Type mapping between different ITPs
LEAN_TO_COQ_TYPE_MAP: Dict[str, str] = {
    "Int": "Z",
    "Nat": "nat",
    "Bool": "bool",
    "String": "string",
    "Char": "ascii",
    "Float": "R",
    "List": "list",
    "Array": "list",
    "Option": "option",
    "Prop": "Prop",
    "Unit": "unit",
    "True": "True",
    "False": "False",
}

COQ_TO_LEAN_TYPE_MAP: Dict[str, str] = {v: k for k, v in LEAN_TO_COQ_TYPE_MAP.items()}


def lean_type_to_coq(lean_type: str) -> str:
    """Convert a Lean type to Coq type.

    Args:
        lean_type: Lean type string.

    Returns:
        Coq type string.
    """
    # Handle simple types
    if lean_type in LEAN_TO_COQ_TYPE_MAP:
        return LEAN_TO_COQ_TYPE_MAP[lean_type]

    # Handle parameterized types (e.g., "List Int" -> "list Z")
    parts = lean_type.split()
    if len(parts) > 1:
        outer = parts[0]
        inner = " ".join(parts[1:])
        if outer in LEAN_TO_COQ_TYPE_MAP:
            coq_outer = LEAN_TO_COQ_TYPE_MAP[outer]
            coq_inner = lean_type_to_coq(inner)
            return f"({coq_outer} {coq_inner})"

    # Handle product types (e.g., "Int × Bool" -> "Z * bool")
    if "×" in lean_type:
        parts = [p.strip() for p in lean_type.split("×")]
        coq_parts = [lean_type_to_coq(p) for p in parts]
        return " * ".join(coq_parts)

    # Return as-is if no mapping found
    return lean_type


def coq_type_to_lean(coq_type: str) -> str:
    """Convert a Coq type to Lean type.

    Args:
        coq_type: Coq type string.

    Returns:
        Lean type string.
    """
    # Handle simple types
    if coq_type in COQ_TO_LEAN_TYPE_MAP:
        return COQ_TO_LEAN_TYPE_MAP[coq_type]

    # Handle parameterized types
    if coq_type.startswith("(") and coq_type.endswith(")"):
        inner = coq_type[1:-1]
        parts = inner.split(None, 1)
        if len(parts) > 1:
            outer = parts[0]
            param = parts[1]
            if outer in COQ_TO_LEAN_TYPE_MAP:
                lean_outer = COQ_TO_LEAN_TYPE_MAP[outer]
                lean_param = coq_type_to_lean(param)
                return f"{lean_outer} {lean_param}"

    # Handle product types (e.g., "Z * bool" -> "Int × Bool")
    if " * " in coq_type:
        parts = [p.strip() for p in coq_type.split("*")]
        lean_parts = [coq_type_to_lean(p) for p in parts]
        return " × ".join(lean_parts)

    # Return as-is if no mapping found
    return coq_type


# Common operators mapping
LEAN_TO_COQ_OPERATORS: Dict[str, str] = {
    "∧": "/\\",
    "∨": "\\/",
    "¬": "~",
    "→": "->",
    "↔": "<->",
    "≠": "<>",
    "≤": "<=",
    "≥": ">=",
    "∈": "In",  # For list membership
    "∉": "~In",
}
