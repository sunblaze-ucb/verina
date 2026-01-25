"""Coq specific template rendering implementation.

This module provides the Coq-specific template engine for rendering
benchmark code, specifications, proofs, and tests.

Uses bool-based specifications with Compute for fast evaluation.
Both preconditions and postconditions return bool for instant decidability.
"""

from typing import Any, List

from verina.dataset.schema import Parameter, RejectInput, Signature, TestCase
from verina.itp.base import ITPTemplate
from verina.coq.types import lean_type_to_coq


# =============================================================================
# Standard imports for Coq tasks
# =============================================================================
# NOTE: String/Ascii imported BEFORE List so that List.length is not shadowed
# by String.length. This is the single source of truth - used by both
# translator (translate_lean_to_coq.py) and test rendering.

STANDARD_COQ_IMPORTS = """Require Import Bool.
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope."""

# Additional imports for testing (tactics, equality schemes)
# NOTE: With bool-based specs, we use Compute for instant evaluation.
# No custom tactics needed - just equality schemes for compound types.
STANDARD_COQ_TEST_EXTRAS = """Require Import Lia.
Require Import Arith.

(* Generate boolean equality functions for compound types *)
Scheme Equality for list.
Scheme Equality for prod.
Scheme Equality for option."""


class CoqGenerationTaskTemplate(ITPTemplate):
    """Coq template engine implementing ITPTemplate interface.

    Renders Coq code for code generation, specification, proofs, and testing.
    Uses bool-based specifications with Compute for instant evaluation.
    Both preconditions and postconditions return bool for decidability.
    """

    # Test message markers (same format as Lean for consistency)
    CODE_TEST_MSG_MARKER = "code_test"
    PRECOND_TEST_DECIDABLE_MSG_MARKER = "precond_test_decidable"
    POSTCOND_TEST_DECIDABLE_MSG_MARKER = "postcond_test_decidable"

    # Error/success messages for test evaluation
    DECIDABLE_ERR_MSG = "The command has indeed failed"
    DECIDABLE_UNKNOWN_MSG = "Cannot infer"
    COMPUTE_SUCCESS_MSG = "= true"

    @staticmethod
    def PRECOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        return f"precond_test_undecidable_{type_}"

    @staticmethod
    def POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        return f"postcond_test_undecidable_{type_}"

    def __init__(self, signature: Signature, use_coq_types: bool = True):
        """Initialize CoqGenerationTaskTemplate.

        Args:
            signature: Function signature (may use Lean types if from shared dataset).
            use_coq_types: If True, convert Lean types to Coq types automatically.
        """
        self.signature = signature
        self.use_coq_types = use_coq_types

    def _get_type(self, type_str: str) -> str:
        """Get the appropriate type string, converting if needed."""
        if self.use_coq_types:
            return lean_type_to_coq(type_str)
        return type_str

    def _parse_coq_type(self, coq_type: str) -> tuple:
        """Parse a Coq type string into a structured representation.

        Returns a tuple of (type_name, [inner_types]) where:
        - Primitives: ("Z", []), ("nat", []), ("bool", []), ("string", [])
        - Lists: ("list", [inner_type])
        - Options: ("option", [inner_type])
        - Products/tuples: ("prod", [type1, type2])

        Examples:
        - "Z" -> ("Z", [])
        - "(list Z)" -> ("list", [("Z", [])])
        - "(Z * nat)" -> ("prod", [("Z", []), ("nat", [])])
        - "(list (Z * Z))" -> ("list", [("prod", [("Z", []), ("Z", [])])])
        - "(option (nat * nat))" -> ("option", [("prod", [("nat", []), ("nat", [])])])
        """
        coq_type = coq_type.strip()

        # Remove outer parentheses if present
        while coq_type.startswith('(') and coq_type.endswith(')'):
            # Check if these parens are matched (not just coincidental)
            depth = 0
            matched = True
            for i, c in enumerate(coq_type[:-1]):  # Skip last char
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                if depth == 0 and i > 0:
                    matched = False
                    break
            if matched:
                coq_type = coq_type[1:-1].strip()
            else:
                break

        # Check for product type (A * B)
        # Need to find * at depth 0
        depth = 0
        star_pos = -1
        for i, c in enumerate(coq_type):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == '*' and depth == 0:
                star_pos = i
                break

        if star_pos > 0:
            left = coq_type[:star_pos].strip()
            right = coq_type[star_pos+1:].strip()
            return ("prod", [self._parse_coq_type(left), self._parse_coq_type(right)])

        # Check for type constructor (list X, option X)
        parts = coq_type.split(None, 1)  # Split on first whitespace
        if len(parts) == 2:
            constructor = parts[0].lower()
            inner = parts[1].strip()
            if constructor in ("list", "option"):
                return (constructor, [self._parse_coq_type(inner)])

        # Primitive type
        return (coq_type, [])

    def _generate_equality_expr(self, parsed_type: tuple, val1: str, val2: str) -> str:
        """Generate an equality expression for a parsed type.

        Args:
            parsed_type: Tuple from _parse_coq_type
            val1, val2: The two values to compare

        Returns:
            A Coq expression that evaluates to bool
        """
        type_name, inner_types = parsed_type
        type_lower = type_name.lower()

        # Primitive types
        if type_lower == "z":
            return f"Z.eqb {val1} {val2}"
        elif type_lower == "nat":
            return f"Nat.eqb {val1} {val2}"
        elif type_lower == "bool":
            return f"Bool.eqb {val1} {val2}"
        elif type_lower == "string":
            return f"String.eqb {val1} {val2}"

        # Compound types
        elif type_lower == "list":
            inner_eq_fn = self._get_inner_equality_fn(inner_types[0])
            return f"list_beq _ {inner_eq_fn} {val1} {val2}"
        elif type_lower == "option":
            inner_eq_fn = self._get_inner_equality_fn(inner_types[0])
            return f"option_beq _ {inner_eq_fn} {val1} {val2}"
        elif type_lower == "prod":
            eq_fn1 = self._get_inner_equality_fn(inner_types[0])
            eq_fn2 = self._get_inner_equality_fn(inner_types[1])
            return f"prod_beq _ _ {eq_fn1} {eq_fn2} {val1} {val2}"
        else:
            # Unknown type - fallback to eqb (may not work)
            return f"eqb {val1} {val2}"

    def _get_inner_equality_fn(self, parsed_type: tuple) -> str:
        """Get the equality function for use as an argument to list_beq/option_beq/prod_beq.

        Returns a function of type (A -> A -> bool) for the given type.
        """
        type_name, inner_types = parsed_type
        type_lower = type_name.lower()

        # Primitive types - return the equality function directly
        if type_lower == "z":
            return "Z.eqb"
        elif type_lower == "nat":
            return "Nat.eqb"
        elif type_lower == "bool":
            return "Bool.eqb"
        elif type_lower == "string":
            return "String.eqb"
        elif type_lower == "ascii":
            return "Ascii.eqb"

        # Compound types - need to build a lambda or partial application
        elif type_lower == "list":
            inner_eq_fn = self._get_inner_equality_fn(inner_types[0])
            return f"(list_beq _ {inner_eq_fn})"
        elif type_lower == "option":
            inner_eq_fn = self._get_inner_equality_fn(inner_types[0])
            return f"(option_beq _ {inner_eq_fn})"
        elif type_lower == "prod":
            eq_fn1 = self._get_inner_equality_fn(inner_types[0])
            eq_fn2 = self._get_inner_equality_fn(inner_types[1])
            return f"(prod_beq _ _ {eq_fn1} {eq_fn2})"
        else:
            return "eqb"

    def _get_equality_fn(self, coq_type: str) -> str:
        """Get the appropriate equality function for a Coq type.

        Different types in Coq require different equality functions:
        - Z (integers): Z.eqb
        - nat: Nat.eqb
        - bool: Bool.eqb
        - string: String.eqb
        - list T: list_beq with inner equality function
        - option T: option_beq with inner equality function
        - T1 * T2: prod_beq with two inner equality functions

        Returns a function suitable for use as (eq_fn val1 val2).
        """
        parsed = self._parse_coq_type(coq_type)
        return self._get_inner_equality_fn(parsed)

    # ==========================================================================
    # ITPTemplate interface implementation
    # ==========================================================================

    def get_name(self) -> str:
        return "coq"

    def get_decidable_err_msg(self) -> str:
        return self.DECIDABLE_ERR_MSG

    def get_decidable_unknown_msg(self) -> str:
        return self.DECIDABLE_UNKNOWN_MSG

    def get_pbt_success_msg(self) -> str:
        # Not used for Coq - we use auto tactics, not QuickChick PBT
        return ""

    def get_pbt_failed_msg(self) -> str:
        # Not used for Coq - we use auto tactics, not QuickChick PBT
        return ""

    def get_pbt_gave_up_msg(self) -> str:
        # Not used for Coq - we use auto tactics, not QuickChick PBT
        return ""

    def get_pbt_test_command(self) -> str:
        # Not used for Coq - we use auto tactics, not QuickChick PBT
        return ""

    def get_cheat_codes(self) -> List[str]:
        return ["admit", "Admitted", "Abort"]

    # ==========================================================================
    # Rendering methods
    # ==========================================================================

    def render_imports(self, imports: str, type_: str) -> str:
        rendered = f"(* !benchmark @start import type={type_} *)\n"
        rendered += imports
        rendered += "\n(* !benchmark @end import *)\n"
        return rendered

    def render_aux(self, aux: str, type_: str) -> str:
        rendered = f"(* !benchmark @start {type_}_aux *)\n"
        rendered += aux
        rendered += f"\n(* !benchmark @end {type_}_aux *)\n"
        return rendered

    def render_test_imports(self) -> str:
        """Render extra imports needed for testing (Compute-based Bool evaluation).

        NOTE: This only adds TEST EXTRAS (Lia, Arith, Scheme Equality, tactics).
        The base imports (STANDARD_COQ_IMPORTS) should already be in the content
        being tested (from task_imports parsed from task.v).

        Since both precond and postcond return bool, we use Compute for instant
        evaluation instead of slow ATP tactics like hammer.
        """
        # Only add test extras - base imports are already in the content
        return self.render_imports(STANDARD_COQ_TEST_EXTRAS, "test")

    def render_param_list(self) -> str:
        """Render Coq parameter list: (a : Z) (b : Z)"""
        rendered = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f"({param.param_name} : {coq_type}) "
        return rendered.strip()

    def render_coq_content(self, coq_content: str) -> str:
        """Render Coq content with proper indentation."""
        if coq_content is None:
            return ""
        rendered = ""
        indented = coq_content.startswith("  ")
        for line in coq_content.splitlines():
            if indented:
                rendered += line + "\n"
            else:
                rendered += "  " + line + "\n"
        return rendered

    def render_full_precond_name(self, *, precond_name: str = "") -> str:
        if precond_name == "":
            return f"{self.signature.name}_precond"
        return f"{self.signature.name}_precond_{precond_name}"

    def render_precond_signature(self, *, precond_name: str = "") -> str:
        """Render precondition signature with bool return type."""
        rendered = f"Definition {self.render_full_precond_name(precond_name=precond_name)} "
        rendered += self.render_param_list()
        rendered += " : bool"  # Bool for fast Compute evaluation
        return rendered

    def render_precond(self, precond: str, *, precond_name: str = "") -> str:
        rendered = self.render_precond_signature(precond_name=precond_name)
        rendered += f" :=\n  (* !benchmark @start precond *)\n{self.render_coq_content(precond)}  (* !benchmark @end precond *).\n"
        return rendered

    def render_precond_hypothesis(self, *, precond_name: str = "") -> str:
        """Render precondition hypothesis.

        Note: With bool-based preconditions, this is no longer used in code signatures.
        Kept for backward compatibility with any code that references it.
        """
        rendered = (
            f"(h_precond : {self.render_full_precond_name(precond_name=precond_name)}"
        )
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += " = true)"  # Bool precondition as equality
        return rendered

    def render_code_signature(self, *, precond_name: str = "") -> str:
        """Render code signature without h_precond parameter.

        With bool-based preconditions, the code no longer takes a precondition
        proof term. The precondition is checked separately as a boolean.
        """
        coq_return_type = self._get_type(self.signature.return_type)
        rendered = f"Definition {self.signature.name} "
        rendered += self.render_param_list()
        # No h_precond parameter - precond is bool, checked separately
        rendered += f" : {coq_return_type}"
        return rendered

    def render_code(self, code: str, *, precond_name: str = "") -> str:
        rendered = self.render_code_signature(precond_name=precond_name)
        rendered += f" :=\n  (* !benchmark @start code *)\n{self.render_coq_content(code)}  (* !benchmark @end code *).\n"
        return rendered

    def render_full_postcond_name(self, *, postcond_name: str = "") -> str:
        if postcond_name == "":
            return f"{self.signature.name}_postcond"
        return f"{self.signature.name}_postcond_{postcond_name}"

    def render_postcond(
        self, postcond: str, *, precond_name: str = "", postcond_name: str = ""
    ) -> str:
        """Render postcondition with bool return type.

        With bool-based specifications:
        - Postcond returns bool for fast Compute evaluation
        - No h_precond parameter (precond is a separate bool check)
        """
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)
        coq_return_type = self._get_type(self.signature.return_type)
        rendered = f"Definition {full_postcond_name} "
        rendered += self.render_param_list()
        # Bool return type, no h_precond parameter
        rendered += f" (result : {coq_return_type}) : bool :=\n"
        rendered += f"  (* !benchmark @start postcond *)\n{self.render_coq_content(postcond)}  (* !benchmark @end postcond *).\n"
        return rendered

    def render_code_and_postcond(
        self,
        code: str,
        postcond: str,
        *,
        precond_name: str = "",
        postcond_name: str = "",
    ) -> str:
        rendered = self.render_code(code, precond_name=precond_name)
        rendered += "\n\n"
        rendered += self.render_postcond(
            postcond, precond_name=precond_name, postcond_name=postcond_name
        )
        return rendered

    def render_theorem_name(self, *, postcond_name: str = "") -> str:
        return (
            self.render_full_postcond_name(postcond_name=postcond_name) + "_satisfied"
        )

    def render_proof(
        self,
        proof: str,
        *,
        precond_name: str = "",
        postcond_name: str = "",
    ) -> str:
        """Render proof theorem with bool-based goal format.

        New goal format: precond params = true -> postcond params (code params) = true
        - Precondition is now a premise (assumption), not a type parameter
        - Tactics: intro H_precond; native_compute; reflexivity
        """
        full_precond_name = self.render_full_precond_name(precond_name=precond_name)
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)

        rendered = f"Theorem {self.render_theorem_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"

        # New goal format: precond = true -> postcond (code) = true
        rendered += f" :\n    {full_precond_name}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += f" = true ->\n    {full_postcond_name}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += f" ({self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += ") = true.\n"
        rendered += "Proof.\n"
        rendered += f"  (* !benchmark @start proof *)\n{self.render_coq_content(proof)}  (* !benchmark @end proof *)\n"
        # Use Admitted if proof contains admit, otherwise Qed
        if "admit" in proof.lower():
            rendered += "Admitted.\n"
        else:
            rendered += "Qed.\n"
        return rendered

    def render_full_task_file(
        self,
        task_imports: str,
        solution_imports: str,
        task_aux: str,
        solution_aux: str,
        precond_aux: str,
        precond: str,
        code_aux: str,
        code: str,
        postcond_aux: str,
        postcond: str,
        proof_aux: str,
        proof: str = "admit.",
    ) -> str:
        """Render a complete task.v file with bool-based signatures.

        This is the single source of truth for task.v file structure.
        Used by both the translator and the fix script to ensure consistency.

        Args:
            task_imports: Imports for task (derived from signature types)
            solution_imports: Additional imports for solution code
            task_aux: Task-level type definitions (Record, Inductive, etc.)
            solution_aux: Helper definitions shared by code and specs
            precond_aux: Helper definitions for precondition
            precond: Precondition body (bool expression)
            code_aux: Helper definitions for code
            code: Code body
            postcond_aux: Helper definitions for postcondition
            postcond: Postcondition body (bool expression)
            proof_aux: Helper definitions for proof
            proof: Proof body (tactics)

        Returns:
            Complete task.v file content with correct bool-based signatures.
        """
        content = self.render_imports(task_imports, "task")
        content += "\n"
        content += self.render_imports(solution_imports, "solution")
        content += "\n"
        content += self.render_aux(task_aux, "task")
        content += "\n"
        content += self.render_aux(solution_aux, "solution")
        content += "\n"
        content += self.render_aux(precond_aux, "precond")
        content += "\n"
        content += self.render_precond(precond)
        content += "\n"
        content += self.render_aux(code_aux, "code")
        content += "\n"
        content += self.render_code(code)
        content += "\n"
        content += self.render_aux(postcond_aux, "postcond")
        content += "\n"
        content += self.render_postcond(postcond)
        content += "\n"
        content += self.render_aux(proof_aux, "proof")
        content += "\n"
        content += self.render_proof(proof)
        return content

    @staticmethod
    def _wrap_parens(value: str) -> str:
        """Wrap value in parentheses if not already wrapped or bracketed."""
        if not value:
            return value
        # Already parenthesized or bracketed
        if (value.startswith('(') and value.endswith(')')) or \
           (value.startswith('[') and value.endswith(']')):
            return value
        return f"({value})"

    @staticmethod
    def render_unit_test_value(coq_type: str, value: Any) -> str:
        """Render a value literal in Coq syntax.

        If value is already a Coq literal string (contains %Z, %string, %nat, or
        is a Coq-style list like "[1; 2]"), return it as-is. Otherwise, convert
        the value to Coq syntax based on the type.

        All values are wrapped in parentheses to ensure correct parsing in
        function application context (e.g., "Some 1" -> "(Some 1)").
        """
        import json

        # Check if value is already a Coq literal (pre-formatted in coq_test.json)
        if isinstance(value, str):
            # Check for common Coq literal markers
            if '%Z' in value or '%string' in value or '%nat' in value or '%char' in value:
                return CoqGenerationTaskTemplate._wrap_parens(value)
            # Check for Coq-style list syntax (semicolon separator)
            if value.startswith('[') and ';' in value:
                return value
            # Check for empty list
            if value == '[]':
                return value
            # Any other string value - wrap in parens
            return CoqGenerationTaskTemplate._wrap_parens(value)

        # Normalize type
        coq_type_lower = coq_type.lower()

        if coq_type_lower == "bool":
            return CoqGenerationTaskTemplate._wrap_parens(str(value).lower())
        elif coq_type_lower == "string":
            return f'("{value}"%string)'
        elif coq_type_lower == "z":
            # Z type (integers)
            return f"({value})%Z"
        elif coq_type_lower == "nat":
            return CoqGenerationTaskTemplate._wrap_parens(str(value))
        elif coq_type_lower == "ascii":
            return f'("{value}")'
        elif coq_type_lower.startswith("list"):
            # Handle list values
            list_value = value
            # Parse string representation of list (e.g., "[2, 2, 3]")
            if isinstance(value, str):
                try:
                    list_value = json.loads(value)
                except json.JSONDecodeError:
                    # If not valid JSON, return as-is but convert commas to semicolons
                    return value.replace(", ", "; ")
            if isinstance(list_value, list):
                items = [CoqGenerationTaskTemplate.render_unit_test_value("Z", v) for v in list_value]
                return "[" + "; ".join(items) + "]"
            return CoqGenerationTaskTemplate._wrap_parens(str(value))
        else:
            return CoqGenerationTaskTemplate._wrap_parens(str(value))

    def render_code_unit_test(self, test_case: TestCase, *, test_idx: int, precond_name: str = "") -> str:
        """Render a Compute-based unit test for code.

        Uses type-specific equality functions (e.g., Z.eqb for integers).
        With bool-based preconditions, code no longer takes h_precond parameter.

        Output format:
            Definition _m_code_test_0 := tt. Print _m_code_test_0.
            Compute (Z.eqb (fn args) expected).
        Expected result in output:
            _m_code_test_0 = tt : unit
            = true : bool
        """
        coq_return_type = self._get_type(self.signature.return_type)

        # Build argument string
        args_str = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            args_str += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"

        # Build the code call and expected value
        code_call = f"({self.signature.name}{args_str})"
        expected = self.render_unit_test_value(coq_return_type, test_case.expected)

        # Generate equality expression using recursive type parser
        parsed_type = self._parse_coq_type(coq_return_type)
        eq_expr = self._generate_equality_expr(parsed_type, code_call, expected)

        # Add marker Definition + Print so we can correlate output with test index
        marker_name = f"_m_{self.CODE_TEST_MSG_MARKER}_{test_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Compute ({eq_expr})."
        return rendered


    def render_precond_unit_test_sound_decidable(
        self, test_case: TestCase, *, test_idx: int, precond_name: str = ""
    ) -> str:
        """Render Compute-based precondition soundness test.

        Tests that precond evaluates to true for valid input using Compute.
        With bool-based preconditions, this is instant evaluation.

        Expected output: = true : bool (for valid inputs)
        """
        full_precond_name = self.render_full_precond_name(precond_name=precond_name)

        # Build argument string
        args_str = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            args_str += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"

        # Use Compute for instant bool evaluation
        marker_name = f"_m_{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Compute ({full_precond_name}{args_str})."

        return rendered

    def render_precond_unit_test_sound_quickchick(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        inverse: bool,
        precond_name: str = "",
    ) -> str:
        """Render QuickChick-based precondition soundness test."""
        rendered = f'(* <{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(self.UNDECIDABLE_QUICKCHICK)}>{test_idx}</{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(self.UNDECIDABLE_QUICKCHICK)}> *)\n'
        rendered += "QuickChick ("
        if inverse:
            rendered += "negb ("
        rendered += f"{self.render_full_precond_name(precond_name=precond_name)}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        if inverse:
            rendered += ")"
        rendered += ")."
        return rendered

    def render_precond_unit_test_complete_decidable(
        self, reject_input: RejectInput, *, test_idx: int, precond_name: str = ""
    ) -> str:
        """Render Compute-based precondition completeness test.

        Tests that precond evaluates to false for invalid/rejected input using Compute.
        With bool-based preconditions, this is instant evaluation.

        Expected output: = false : bool (for invalid/rejected inputs)
        """
        full_precond_name = self.render_full_precond_name(precond_name=precond_name)

        # Build argument string
        args_str = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            args_str += f" {self.render_unit_test_value(coq_type, reject_input.input[param.param_name])}"

        # Use Compute for instant bool evaluation
        # Use _c suffix to distinguish complete tests from sound tests
        marker_name = f"_m_{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}_c"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Compute ({full_precond_name}{args_str})."

        return rendered

    def render_postcond_unit_test_complete_decidable(
        self, test_case: TestCase, *, test_idx: int, precond_name: str = "", postcond_name: str = ""
    ) -> str:
        """Render Compute-based postcondition completeness test.

        Tests that postcond evaluates to true for expected output using Compute.
        With bool-based postconditions, this is instant evaluation.
        No h_precond parameter needed since postcond is now bool.

        Expected output: = true : bool (for expected outputs)
        """
        coq_return_type = self._get_type(self.signature.return_type)
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)

        # Build argument string
        args_str = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            args_str += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        expected_str = self.render_unit_test_value(coq_return_type, test_case.expected)

        # Use Compute for instant bool evaluation - no H parameter needed
        # Use _c suffix to distinguish complete tests from sound tests
        marker_name = f"_m_{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}_c"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Compute ({full_postcond_name}{args_str} {expected_str})."

        return rendered

    def render_postcond_unit_test_sound_decidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        unexpected_idx: int,
        precond_name: str = "",
        postcond_name: str = "",
    ) -> str:
        """Render Compute-based postcondition soundness test.

        Tests that postcond evaluates to false for unexpected output using Compute.
        With bool-based postconditions, this is instant evaluation.
        No h_precond parameter needed since postcond is now bool.

        Expected output: = false : bool (for unexpected outputs)
        """
        coq_return_type = self._get_type(self.signature.return_type)
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)

        # Build argument string
        args_str = ""
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            args_str += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        unexpected_str = self.render_unit_test_value(coq_return_type, test_case.unexpected[unexpected_idx])

        # Use Compute for instant bool evaluation - no H parameter needed
        marker_name = f"_m_{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}_{unexpected_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Compute ({full_postcond_name}{args_str} {unexpected_str})."

        return rendered

    # ==========================================================================
    # Formal verification rendering methods
    # ==========================================================================
    #
    # Note: For formal verification proofs comparing ground truth vs generated specs,
    # we use "= true" assertions since both precond and postcond are now bool.
    # The lemmas prove: if ground_truth = true, then generated = true (or vice versa).

    def render_precond_formal_soundness(
        self,
        generated_precond: str,
        ground_truth_precond: str,
        proof: str,
    ) -> str:
        """Prove: if ground_truth_precond = true, then generated_precond = true."""
        rendered = "Lemma precond_soundness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    ({ground_truth_precond}) = true -> ({generated_precond}) = true.\n"
        rendered += "Proof.\n"
        rendered += self.render_coq_content(proof)
        rendered += "Qed.\n"
        return rendered

    def render_precond_formal_completeness(
        self, generated_precond: str, ground_truth_precond: str, proof: str
    ) -> str:
        """Prove: if generated_precond = true, then ground_truth_precond = true."""
        rendered = "Lemma precond_completeness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    ({generated_precond}) = true -> ({ground_truth_precond}) = true.\n"
        rendered += "Proof.\n"
        rendered += self.render_coq_content(proof)
        rendered += "Qed.\n"
        return rendered

    def render_postcond_formal_soundness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        r"""Prove: if ground_truth_precond = true /\ generated_postcond = true,
        then ground_truth_postcond = true."""
        rendered = "Lemma postcond_soundness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    (({ground_truth_precond}) = true /\\ ({generated_postcond}) = true) -> ({ground_truth_postcond}) = true.\n"
        rendered += "Proof.\n"
        rendered += self.render_coq_content(proof)
        rendered += "Qed.\n"
        return rendered

    def render_postcond_formal_completeness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        r"""Prove: if ground_truth_precond = true /\ ground_truth_postcond = true,
        then generated_postcond = true."""
        rendered = "Lemma postcond_completeness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    (({ground_truth_precond}) = true /\\ ({ground_truth_postcond}) = true) -> ({generated_postcond}) = true.\n"
        rendered += "Proof.\n"
        rendered += self.render_coq_content(proof)
        rendered += "Qed.\n"
        return rendered


# Export public API
__all__ = [
    "CoqGenerationTaskTemplate",
]


if __name__ == "__main__":
    signature = Signature(
        name="foo",
        parameters=[Parameter(param_name="x", param_type="Int")],
        return_type="Int",
    )
    template = CoqGenerationTaskTemplate(signature)
    # Bool-based specs: precond and postcond return bool
    precond = "true"  # Bool: always true precondition
    code = "(x + 1)%Z"
    # Bool postcond: check property, not algorithm restatement
    spec = "(result >? x)%Z"  # result > x (property check)
    proof = "intro H_precond. native_compute. reflexivity."
    test_case = TestCase(input={"x": 1}, expected=2, unexpected=[3])

    rendered_precond = template.render_precond(precond)
    rendered_code = template.render_code(code)
    rendered_spec = template.render_postcond(spec, postcond_name="add_one")
    rendered_proof = template.render_proof(proof, postcond_name="add_one")
    rendered_code_unit_test = template.render_code_unit_test(test_case, test_idx=0)
    rendered_precond_unit_test_sound_decidable = (
        template.render_precond_unit_test_sound_decidable(test_case, test_idx=0)
    )
    rendered_postcond_unit_test_complete_decidable = (
        template.render_postcond_unit_test_complete_decidable(test_case, test_idx=0)
    )

    print("=" * 60)
    print("Precond (bool):")
    print(rendered_precond)
    print("=" * 60)
    print("Code (no h_precond):")
    print(rendered_code)
    print("=" * 60)
    print("Postcond (bool, no h_precond):")
    print(rendered_spec)
    print("=" * 60)
    print("Proof (precond=true -> postcond=true):")
    print(rendered_proof)
    print("=" * 60)
    print("Code unit test (Compute-based):")
    print(rendered_code_unit_test)
    print("=" * 60)
    print("Precond unit test (Compute-based):")
    print(rendered_precond_unit_test_sound_decidable)
    print("=" * 60)
    print("Postcond unit test (Compute-based):")
    print(rendered_postcond_unit_test_complete_decidable)
