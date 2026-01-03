"""Coq type utilities.

This module provides type mapping utilities for Coq, including
conversion between Lean and Coq types.
"""

from typing import Dict

# Lean to Coq type mapping
LEAN_TO_COQ_TYPE_MAP: Dict[str, str] = {
    # Basic types
    "Int": "Z",
    "Nat": "nat",
    "Bool": "bool",
    "String": "string",
    "Char": "ascii",
    "Float": "R",
    "Unit": "unit",

    # Parameterized types
    "List": "list",
    "Array": "list",
    "Option": "option",

    # Logical types
    "Prop": "Prop",
    "True": "True",
    "False": "False",
}

# Reverse mapping
COQ_TO_LEAN_TYPE_MAP: Dict[str, str] = {v: k for k, v in LEAN_TO_COQ_TYPE_MAP.items()}


def lean_type_to_coq(lean_type: str) -> str:
    """Convert a Lean type to Coq type.

    Args:
        lean_type: Lean type string.

    Returns:
        Coq type string.

    Examples:
        >>> lean_type_to_coq("Int")
        'Z'
        >>> lean_type_to_coq("List Int")
        '(list Z)'
        >>> lean_type_to_coq("Int × Bool")
        'Z * bool'
        >>> lean_type_to_coq("List (Nat × Nat)")
        '(list (nat * nat))'
    """
    lean_type = lean_type.strip()

    # Handle simple types
    if lean_type in LEAN_TO_COQ_TYPE_MAP:
        return LEAN_TO_COQ_TYPE_MAP[lean_type]

    # Handle parenthesized types first - strip parens and convert inner
    # This handles cases like "(Nat × Nat)" -> "(nat * nat)"
    if lean_type.startswith("(") and lean_type.endswith(")"):
        inner = lean_type[1:-1].strip()
        converted_inner = lean_type_to_coq(inner)
        # Only wrap in parens if not already wrapped
        if converted_inner.startswith("("):
            return converted_inner
        return f"({converted_inner})"

    # Handle parameterized types (e.g., "List Int" -> "(list Z)")
    parts = lean_type.split(None, 1)  # Split on first whitespace
    if len(parts) > 1:
        outer = parts[0]
        inner = parts[1]
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

    Examples:
        >>> coq_type_to_lean("Z")
        'Int'
        >>> coq_type_to_lean("(list Z)")
        'List Int'
    """
    coq_type = coq_type.strip()

    # Handle simple types
    if coq_type in COQ_TO_LEAN_TYPE_MAP:
        return COQ_TO_LEAN_TYPE_MAP[coq_type]

    # Handle parameterized types
    if coq_type.startswith("(") and coq_type.endswith(")"):
        inner = coq_type[1:-1].strip()
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


# Common Coq library imports for different types
COQ_TYPE_IMPORTS: Dict[str, str] = {
    "Z": "Require Import ZArith.\nOpen Scope Z_scope.",
    "nat": "",  # Built-in
    "bool": "Require Import Bool.",
    "string": "Require Import String.",
    "ascii": "Require Import Ascii.",
    "R": "Require Import Reals.\nOpen Scope R_scope.",
    "list": "Require Import List.\nImport ListNotations.",
    "option": "",  # Built-in
}


def get_coq_imports_for_types(types: list[str]) -> str:
    """Get required Coq imports for a list of types.

    Args:
        types: List of Coq types.

    Returns:
        String of Coq import statements.
    """
    imports = set()
    for t in types:
        # Extract base type
        base_type = t.strip()
        if base_type.startswith("("):
            # Parameterized type - get both outer and inner
            parts = base_type[1:-1].split(None, 1)
            if parts:
                base_type = parts[0]
                if len(parts) > 1:
                    inner_import = get_coq_imports_for_types([parts[1]])
                    if inner_import:
                        imports.add(inner_import)

        if base_type in COQ_TYPE_IMPORTS and COQ_TYPE_IMPORTS[base_type]:
            imports.add(COQ_TYPE_IMPORTS[base_type])

    return "\n".join(sorted(imports))


# Lean to Coq operator mapping
LEAN_TO_COQ_OPERATORS: Dict[str, str] = {
    "∧": "/\\",
    "∨": "\\/",
    "¬": "~",
    "→": "->",
    "↔": "<->",
    "≠": "<>",
    "≤": "<=",
    "≥": ">=",
    "∈": "In",
    "∉": "~In",
    "++": "++",  # List append (same in both)
}


def lean_expr_to_coq(lean_expr: str) -> str:
    """Convert a Lean expression to Coq expression.

    This performs basic operator substitution. For more complex
    expressions, manual conversion may be needed.

    Args:
        lean_expr: Lean expression string.

    Returns:
        Coq expression string.
    """
    result = lean_expr
    for lean_op, coq_op in LEAN_TO_COQ_OPERATORS.items():
        result = result.replace(lean_op, coq_op)
    return result


# Export public API
__all__ = [
    "LEAN_TO_COQ_TYPE_MAP",
    "COQ_TO_LEAN_TYPE_MAP",
    "lean_type_to_coq",
    "coq_type_to_lean",
    "COQ_TYPE_IMPORTS",
    "get_coq_imports_for_types",
    "LEAN_TO_COQ_OPERATORS",
    "lean_expr_to_coq",
]
