"""Coq specific template rendering implementation.

This module provides the Coq-specific template engine for rendering
benchmark code, specifications, proofs, and tests.

Uses auto tactics (lia, intuition, etc.) for spec evaluation.
"""

from typing import Any, List

from verina.dataset.schema import Parameter, RejectInput, Signature, TestCase
from verina.itp.base import ITPTemplate
from verina.coq.types import lean_type_to_coq


class CoqGenerationTaskTemplate(ITPTemplate):
    """Coq template engine implementing ITPTemplate interface.

    Renders Coq code for code generation, specification, proofs, and testing.
    Uses auto tactics for spec evaluation (not QuickChick, which doesn't support Prop).
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

    def _get_equality_fn(self, coq_type: str) -> str:
        """Get the appropriate equality function for a Coq type.

        Different types in Coq require different equality functions:
        - Z (integers): Z.eqb
        - nat: Nat.eqb
        - bool: Bool.eqb
        - string: String.eqb
        """
        coq_type_lower = coq_type.lower()
        if coq_type_lower == "z":
            return "Z.eqb"
        elif coq_type_lower == "nat":
            return "Nat.eqb"
        elif coq_type_lower == "bool":
            return "Bool.eqb"
        elif coq_type_lower == "string":
            return "String.eqb"
        else:
            # Fallback - may not work for all types
            return "eqb"

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
        """Render imports needed for testing (auto tactics).

        Note: Basic imports (ZArith, Bool, List, etc.) should be in the task.v
        preamble which is automatically captured as task_imports.
        This method only adds test-specific imports like Lia for auto tactics.
        """
        imports = """Require Import Lia.
Require Import Arith."""
        return self.render_imports(imports, "test")

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
        rendered = f"Definition {self.render_full_precond_name(precond_name=precond_name)} "
        rendered += self.render_param_list()
        rendered += " : Prop"
        return rendered

    def render_precond(self, precond: str, *, precond_name: str = "") -> str:
        rendered = self.render_precond_signature(precond_name=precond_name)
        rendered += f" :=\n  (* !benchmark @start precond *)\n{self.render_coq_content(precond)}  (* !benchmark @end precond *).\n"
        return rendered

    def render_precond_hypothesis(self, *, precond_name: str = "") -> str:
        rendered = (
            f"(h_precond : {self.render_full_precond_name(precond_name=precond_name)}"
        )
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += ")"
        return rendered

    def render_code_signature(self, *, precond_name: str = "") -> str:
        coq_return_type = self._get_type(self.signature.return_type)
        rendered = f"Definition {self.signature.name} "
        rendered += self.render_param_list()
        rendered += f" {self.render_precond_hypothesis(precond_name=precond_name)} : {coq_return_type}"
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
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)
        coq_return_type = self._get_type(self.signature.return_type)
        rendered = f"Definition {full_postcond_name} "
        rendered += self.render_param_list()
        rendered += f" (result : {coq_return_type}) {self.render_precond_hypothesis(precond_name=precond_name)} : Prop :=\n"
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
        rendered = f"Theorem {self.render_theorem_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" {self.render_precond_hypothesis(precond_name=precond_name)}"
        rendered += f" :\n    {self.render_full_postcond_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += f" ({self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += " h_precond) h_precond.\n"
        rendered += "Proof.\n"
        rendered += f"  (* !benchmark @start proof *)\n{self.render_coq_content(proof)}  (* !benchmark @end proof *)\n"
        rendered += "Qed.\n"
        return rendered

    @staticmethod
    def render_unit_test_value(coq_type: str, value: Any) -> str:
        """Render a value literal in Coq syntax.

        If value is already a Coq literal string (contains %Z, %string, %nat, or
        is a Coq-style list like "[1; 2]"), return it as-is. Otherwise, convert
        the value to Coq syntax based on the type.
        """
        import json

        # Check if value is already a Coq literal (pre-formatted in coq_test.json)
        if isinstance(value, str):
            # Check for common Coq literal markers
            if '%Z' in value or '%string' in value or '%nat' in value or '%char' in value:
                return value
            # Check for Coq-style list syntax (semicolon separator)
            if value.startswith('[') and ';' in value:
                return value
            # Check for empty list
            if value == '[]':
                return value

        # Normalize type
        coq_type_lower = coq_type.lower()

        if coq_type_lower == "bool":
            return str(value).lower()
        elif coq_type_lower == "string":
            return f'"{value}"%string'
        elif coq_type_lower == "z":
            # Z type (integers)
            return f"({value})%Z"
        elif coq_type_lower == "nat":
            return str(value)
        elif coq_type_lower == "ascii":
            return f'"{value}"'
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
            return str(value)
        else:
            return str(value)

    def render_code_unit_test(self, test_case: TestCase, *, test_idx: int) -> str:
        """Render a Compute-based unit test for code.

        Uses type-specific equality functions (e.g., Z.eqb for integers).
        Output format: Compute (Z.eqb (fn args I) expected).
        Expected result: = true : bool
        """
        coq_return_type = self._get_type(self.signature.return_type)
        equality_fn = self._get_equality_fn(coq_return_type)

        rendered = f'(* <{self.CODE_TEST_MSG_MARKER}>{test_idx}</{self.CODE_TEST_MSG_MARKER}> *)\n'
        rendered += f"Compute ({equality_fn} ({self.signature.name}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        rendered += " I)"  # I is the proof of True
        expected = self.render_unit_test_value(coq_return_type, test_case.expected)
        rendered += f" {expected})."
        return rendered

    # Automation tactics for solving goals without knowing the specific proof
    # These are tried in sequence by `solve [...]` - first success wins
    # Key: `intuition lia` handles most cases (equalities, conjunctions, disjunctions, implications)
    AUTOMATION_TACTICS = (
        "reflexivity | trivial | easy | "
        "lia | nia | tauto | "
        "intuition lia | intuition nia | "
        "firstorder | firstorder lia | "
        "vm_compute; reflexivity | vm_compute; lia"
    )

    # Automation tactics for proving negation (rejecting invalid inputs/outputs)
    # Applied AFTER `intro H` - first success wins
    NEGATION_AUTOMATION_TACTICS = (
        "discriminate | contradiction | "
        "lia | nia | tauto | "
        "intuition lia | easy"
    )

    def render_precond_unit_test_sound_decidable(
        self, test_case: TestCase, *, test_idx: int, precond_name: str = ""
    ) -> str:
        """Render decidable precondition soundness test.

        Tests that precond holds for valid input using Goal/Proof pattern.
        Uses automation tactics (hammer-like) to close the goal without
        knowing the specific proof ahead of time.

        Compilation fails if no automation tactic can prove the precondition.
        Uses Print-based markers instead of comments since Coq comments don't appear in output.
        """
        full_precond_name = self.render_full_precond_name(precond_name=precond_name)
        # Use Print-based marker that appears in output
        marker_name = f"_m_{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Goal {full_precond_name}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        rendered += f".\n  unfold {full_precond_name}.\n"
        rendered += f"  solve [{self.AUTOMATION_TACTICS}].\nQed."
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
        """Render decidable precondition completeness test (should reject).

        Tests that precond rejects invalid input by proving the negation.
        Uses automation tactics to prove ~(precond args).

        Note: For simple preconditions like `True`, this test would fail
        since we can't prove ~True. Such tasks shouldn't have reject_inputs.
        Uses Print-based markers instead of comments since Coq comments don't appear in output.
        """
        full_precond_name = self.render_full_precond_name(precond_name=precond_name)
        # Use Print-based marker that appears in output
        marker_name = f"_m_{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Goal ~({full_precond_name}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, reject_input.input[param.param_name])}"
        rendered += f").\n  unfold {full_precond_name}.\n"
        rendered += f"  intro H.\n"
        rendered += f"  first [{self.NEGATION_AUTOMATION_TACTICS}].\nQed."
        return rendered

    def render_postcond_unit_test_complete_decidable(
        self, test_case: TestCase, *, test_idx: int, postcond_name: str = ""
    ) -> str:
        """Render decidable postcondition completeness test.

        Tests that postcond accepts the expected output using automation tactics.
        Uses hammer-like tactics to close the goal without knowing the proof.
        Uses Print-based markers instead of comments since Coq comments don't appear in output.
        """
        coq_return_type = self._get_type(self.signature.return_type)
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)

        # Use Print-based marker that appears in output
        marker_name = f"_m_{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Goal {full_postcond_name}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        rendered += f" {self.render_unit_test_value(coq_return_type, test_case.expected)} I.\n"
        rendered += f"  unfold {full_postcond_name}.\n"
        rendered += f"  solve [{self.AUTOMATION_TACTICS}].\nQed."
        return rendered

    def render_postcond_unit_test_sound_decidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        unexpected_idx: int,
        postcond_name: str = "",
    ) -> str:
        """Render decidable postcondition soundness test (should reject unexpected).

        Tests that postcond rejects unexpected output by proving the negation.
        Uses automation tactics to prove ~(postcond args unexpected I).
        Uses Print-based markers instead of comments since Coq comments don't appear in output.
        """
        coq_return_type = self._get_type(self.signature.return_type)
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)

        # Use Print-based marker that appears in output (tuple index uses underscore)
        marker_name = f"_m_{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}_{test_idx}_{unexpected_idx}"
        rendered = f'Definition {marker_name} := tt. Print {marker_name}.\n'
        rendered += f"Goal ~({full_postcond_name}"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" {self.render_unit_test_value(coq_type, test_case.input[param.param_name])}"
        rendered += f" {self.render_unit_test_value(coq_return_type, test_case.unexpected[unexpected_idx])} I).\n"
        rendered += f"  unfold {full_postcond_name}.\n"
        rendered += f"  intro H.\n"
        rendered += f"  first [{self.NEGATION_AUTOMATION_TACTICS}].\nQed."
        return rendered

    # ==========================================================================
    # Formal verification rendering methods
    # ==========================================================================

    def render_precond_formal_soundness(
        self,
        generated_precond: str,
        ground_truth_precond: str,
        proof: str,
    ) -> str:
        rendered = "Lemma precond_soundness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    ({ground_truth_precond}) -> ({generated_precond}).\n"
        rendered += "Proof.\n"
        rendered += self.render_coq_content(proof)
        rendered += "Qed.\n"
        return rendered

    def render_precond_formal_completeness(
        self, generated_precond: str, ground_truth_precond: str, proof: str
    ) -> str:
        rendered = "Lemma precond_completeness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    ({generated_precond}) -> ({ground_truth_precond}).\n"
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
        rendered = "Lemma postcond_soundness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    (({ground_truth_precond}) /\\ ({generated_postcond})) -> ({ground_truth_postcond}).\n"
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
        rendered = "Lemma postcond_completeness"
        for param in self.signature.parameters:
            coq_type = self._get_type(param.param_type)
            rendered += f" ({param.param_name} : {coq_type})"
        rendered += f" :\n    (({ground_truth_precond}) /\\ ({ground_truth_postcond})) -> ({generated_postcond}).\n"
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
    precond = "True"
    code = "(x + 1)%Z"
    spec = "result = (x + 1)%Z"
    proof = "reflexivity."
    test_case = TestCase(input={"x": 1}, expected=2, unexpected=[3])

    rendered_precond = template.render_precond(precond)
    rendered_code = template.render_code(code)
    rendered_spec = template.render_postcond(spec, postcond_name="add_one")
    rendered_proof = template.render_proof(proof, postcond_name="add_one")
    rendered_code_unit_test = template.render_code_unit_test(test_case, test_idx=0)
    rendered_precond_unit_test_sound_decidable = (
        template.render_precond_unit_test_sound_decidable(test_case, test_idx=0)
    )

    print("=" * 60)
    print("Precond:")
    print(rendered_precond)
    print("=" * 60)
    print("Code:")
    print(rendered_code)
    print("=" * 60)
    print("Postcond:")
    print(rendered_spec)
    print("=" * 60)
    print("Proof:")
    print(rendered_proof)
    print("=" * 60)
    print("Code unit test:")
    print(rendered_code_unit_test)
    print("=" * 60)
    print("Precond unit test (decidable):")
    print(rendered_precond_unit_test_sound_decidable)
