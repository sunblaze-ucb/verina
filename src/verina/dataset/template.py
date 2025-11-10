from typing import Any

from verina.dataset.schema import Parameter, RejectInput, Signature, TestCase

# TODO: Use jinja2?


class LeanGenerationTaskTemplate:
    CODE_TEST_MSG_MARKER = "code_test"
    PRECOND_TEST_DECIDABLE_MSG_MARKER = "precond_test_decidable"
    POSTCOND_TEST_DECIDABLE_MSG_MARKER = "postcond_test_decidable"

    UNDECIDABLE_SIMP = "simp"
    UNDECIDABLE_PLAUSIBLE = "plausible"
    UNDECIDABLE_LLM = "llm"

    DECIDABLE_ERR_MSG = "did not evaluate to `true`"
    DECIDABLE_UNKNOWN_MSG = "failed to synthesize"
    SIMP_SUCCESS_MSG = "no goals to be solved"
    PLAUSIBLE_SUCCESS_MSG = "Unable to find a counter-example"
    PLAUSIBLE_GAVE_UP_MSG = (
        "Gave up after failing to generate values that fulfill the preconditions"
    )
    PLAUSIBLE_FAILED_MSG = "Found a counter-example!"

    PLAUSIBLE_TEST_COMMAND = "plausible ( config := { numInst := 1000, maxSize := 100, numRetries := 20, randomSeed := some 42})"

    @staticmethod
    def PRECOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        return f"precond_test_undecidable_{type_}"

    @staticmethod
    def POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(type_: str) -> str:
        return f"postcond_test_undecidable_{type_}"

    def __init__(self, signature: Signature):
        self.signature = signature

    def render_imports(self, imports: str, type_: str) -> str:
        rendered = f"-- !benchmark @start import type={type_}\n"
        rendered += imports
        rendered += "\n-- !benchmark @end import\n"
        return rendered

    def render_aux(self, aux: str, type_: str) -> str:
        rendered = f"-- !benchmark @start {type_}_aux\n"
        rendered += aux
        rendered += f"\n-- !benchmark @end {type_}_aux\n"
        return rendered

    def render_test_imports(self) -> str:
        return self.render_imports("import Plausible\nimport Mathlib", "type=test")

    def render_param_list(self) -> str:
        rendered = ""
        for param in self.signature.parameters:
            rendered += f"({param.param_name} : {param.param_type}) "
        return rendered.strip()

    def render_lean_content(self, lean_content: str) -> str:
        if lean_content is None:
            return ""
        rendered = ""
        indented = lean_content.startswith("  ")
        for line in lean_content.splitlines():
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
        rendered = f"@[reducible, simp]\ndef {self.render_full_precond_name(precond_name=precond_name)} "
        rendered += self.render_param_list()
        rendered += " : Prop"
        return rendered

    def render_precond(self, precond: str, *, precond_name: str = "") -> str:
        rendered = self.render_precond_signature(precond_name=precond_name)
        rendered += f" :=\n  -- !benchmark @start precond\n{self.render_lean_content(precond)}  -- !benchmark @end precond\n"
        return rendered

    def render_precond_hypothesis(self, *, precond_name: str = "") -> str:
        rendered = (
            f"(h_precond : {self.render_full_precond_name(precond_name=precond_name)}"
        )
        for param in self.signature.parameters:
            rendered += f" ({param.param_name})"
        rendered += ")"
        return rendered

    def render_code_signature(self, *, precond_name: str = "") -> str:
        rendered = f"def {self.signature.name} "
        rendered += self.render_param_list()
        rendered += f" {self.render_precond_hypothesis(precond_name=precond_name)} : {self.signature.return_type}"
        return rendered

    def render_code(self, code: str, *, precond_name: str = "") -> str:
        rendered = self.render_code_signature(precond_name=precond_name)
        rendered += f" :=\n  -- !benchmark @start code\n{self.render_lean_content(code)}  -- !benchmark @end code\n"
        return rendered

    def render_full_postcond_name(self, *, postcond_name: str = "") -> str:
        if postcond_name == "":
            return f"{self.signature.name}_postcond"
        return f"{self.signature.name}_postcond_{postcond_name}"

    def render_postcond(
        self, postcond: str, *, precond_name: str = "", postcond_name: str = ""
    ) -> str:
        full_postcond_name = self.render_full_postcond_name(postcond_name=postcond_name)
        rendered = f"@[reducible, simp]\ndef {full_postcond_name} "
        rendered += self.render_param_list()
        rendered += f" (result: {self.signature.return_type}) {self.render_precond_hypothesis(precond_name=precond_name)} : Prop :=\n  -- !benchmark @start postcond\n{self.render_lean_content(postcond)}  -- !benchmark @end postcond\n"
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

    def render_theorem_name(self, *, postcond_name: str) -> str:
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
        rendered = f"theorem {self.render_theorem_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" {self.render_precond_hypothesis(precond_name=precond_name)}"
        rendered += (
            f" :\n    {self.render_full_postcond_name(postcond_name=postcond_name)}"
        )
        for param in self.signature.parameters:
            rendered += f" ({param.param_name})"
        rendered += f" ({self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name})"
        rendered += " h_precond) h_precond"
        rendered += f" := by\n  -- !benchmark @start proof\n{self.render_lean_content(proof)}  -- !benchmark @end proof\n"
        return rendered

    @staticmethod
    def render_unit_test_value(lean_type: str, value: Any) -> str:
        if lean_type == "Bool":
            return str(value).lower()
        elif lean_type == "String":
            return f'"{value}"'
        elif lean_type == "Char":
            return f"'{value}'"
        else:
            return str(value)  # Use value as is for other types

    def render_code_unit_test(self, test_case: TestCase, *, test_idx: int) -> str:
        rendered = f'#print "<{self.CODE_TEST_MSG_MARKER}>{test_idx}</{self.CODE_TEST_MSG_MARKER}>"\n\n'
        rendered += f"#guard {self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" (by sorry) == ({self.render_unit_test_value(self.signature.return_type, test_case.expected)})"
        return rendered

    def render_precond_unit_test_sound_decidable(
        self, test_case: TestCase, *, test_idx: int, precond_name: str = ""
    ) -> str:
        rendered = f'#print "<{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}>{test_idx}</{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}>"\n\n'
        rendered += (
            f"#guard decide ({self.render_full_precond_name(precond_name=precond_name)}"
        )
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += ")"
        return rendered

    def render_precond_unit_test_sound_undecidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        test_type: str,
        test_proof: str,
        inverse: bool,
        precond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        rendered = f'#print "<{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>{test_idx}</{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>"\n\n'
        rendered += "example : "
        if inverse:
            rendered += "¬"
        rendered += f"({self.render_full_precond_name(precond_name=precond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += ") := by\n"
        rendered += f"  unfold {self.render_full_precond_name(precond_name=precond_name)}\n  simp_all! (config := {{ failIfUnchanged := false }})\n"
        if use_grind:
            rendered += "  grind\n"
        rendered += self.render_lean_content(test_proof)
        return rendered

    def render_precond_unit_test_sound_plausible(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        inverse: bool,
        precond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        return self.render_precond_unit_test_sound_undecidable(
            test_case,
            test_idx=test_idx,
            test_type=self.UNDECIDABLE_PLAUSIBLE,
            test_proof=self.PLAUSIBLE_TEST_COMMAND,
            precond_name=precond_name,
            inverse=inverse,
            use_grind=use_grind,
        )

    def render_precond_unit_test_complete_decidable(
        self, reject_input: RejectInput, *, test_idx: int, precond_name: str = ""
    ) -> str:
        rendered = f'#print "<{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}>{test_idx}</{self.PRECOND_TEST_DECIDABLE_MSG_MARKER}>"\n\n'
        rendered += f"#guard decide (¬ ({self.render_full_precond_name(precond_name=precond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, reject_input.input[param.param_name])})"
        rendered += "))"
        return rendered

    def render_precond_unit_test_complete_undecidable(
        self,
        reject_input: RejectInput,
        *,
        test_idx: int,
        test_type: str,
        test_proof: str,
        inverse: bool,
        precond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        rendered = f'#print "<{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>{test_idx}</{self.PRECOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>"\n\n'
        rendered += "example : "
        if not inverse:
            rendered += "¬"
        rendered += f"({self.render_full_precond_name(precond_name=precond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, reject_input.input[param.param_name])})"
        rendered += ") := by\n"
        rendered += f"  unfold {self.render_full_precond_name(precond_name=precond_name)}\n  simp_all! (config := {{ failIfUnchanged := false }})\n"
        if use_grind:
            rendered += "  grind\n"
        rendered += self.render_lean_content(test_proof)
        return rendered

    def render_precond_unit_test_complete_plausible(
        self,
        reject_input: RejectInput,
        *,
        test_idx: int,
        inverse: bool,
        precond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        return self.render_precond_unit_test_complete_undecidable(
            reject_input,
            test_idx=test_idx,
            test_type=self.UNDECIDABLE_PLAUSIBLE,
            test_proof=self.PLAUSIBLE_TEST_COMMAND,
            precond_name=precond_name,
            inverse=inverse,
            use_grind=use_grind,
        )

    def render_postcond_unit_test_complete_decidable(
        self, test_case: TestCase, *, test_idx: int, postcond_name: str = ""
    ) -> str:
        rendered = f'#print "<{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}>{test_idx}</{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}>"\n\n'
        rendered += f"#guard decide ({self.render_full_postcond_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.expected)}) (by sorry))"
        return rendered

    def render_postcond_unit_test_complete_undecidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        test_type: str,
        test_proof: str,
        inverse: bool,
        postcond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        rendered = f'#print "<{self.POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>{test_idx}</{self.POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>"\n\n'
        rendered += "example : "
        if inverse:
            rendered += "¬"
        rendered += f"({self.render_full_postcond_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.expected)}) (by sorry)) := by\n"
        rendered += (
            f"  unfold {self.render_full_postcond_name(postcond_name=postcond_name)}\n"
        )
        rendered += "  simp_all! (config := { failIfUnchanged := false })\n  simp (config := { failIfUnchanged := false }) [*]\n"
        if use_grind:
            rendered += "  grind\n"
        if test_proof != "":
            rendered += self.render_lean_content(test_proof)
        return rendered

    def render_postcond_unit_test_complete_plausible(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        inverse: bool,
        postcond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        return self.render_postcond_unit_test_complete_undecidable(
            test_case,
            test_idx=test_idx,
            postcond_name=postcond_name,
            test_type=self.UNDECIDABLE_PLAUSIBLE,
            test_proof=self.PLAUSIBLE_TEST_COMMAND,
            inverse=inverse,
            use_grind=use_grind,
        )

    def render_postcond_unit_test_sound_decidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        unexpected_idx: int,
        postcond_name: str = "",
    ) -> str:
        rendered = f'#print "<{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}>{test_idx},{unexpected_idx}</{self.POSTCOND_TEST_DECIDABLE_MSG_MARKER}>"\n\n'
        rendered += f"#guard decide (¬ ({self.render_full_postcond_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.unexpected[unexpected_idx])}) (by sorry)"
        rendered += "))"
        return rendered

    def render_postcond_unit_test_sound_undecidable(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        unexpected_idx: int,
        test_type: str,
        test_proof: str,
        inverse: bool,
        postcond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        rendered = f'#print "<{self.POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>{test_idx},{unexpected_idx}</{self.POSTCOND_TEST_UNDECIDABLE_MSG_MARKER(test_type)}>"\n\n'
        rendered += "example : "
        if not inverse:
            rendered += "¬"
        rendered += f"({self.render_full_postcond_name(postcond_name=postcond_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.unexpected[unexpected_idx])}) (by sorry)) := by\n"
        rendered += (
            f"  unfold {self.render_full_postcond_name(postcond_name=postcond_name)}\n"
        )
        rendered += "  simp_all! (config := { failIfUnchanged := false })\n  simp (config := { failIfUnchanged := false }) [*]\n"
        if use_grind:
            rendered += "  grind\n"
        if test_proof != "":
            rendered += self.render_lean_content(test_proof)
        return rendered

    def render_postcond_unit_test_sound_plausible(
        self,
        test_case: TestCase,
        *,
        test_idx: int,
        unexpected_idx: int,
        inverse: bool,
        postcond_name: str = "",
        use_grind: bool = False,
    ) -> str:
        return self.render_postcond_unit_test_sound_undecidable(
            test_case,
            test_idx=test_idx,
            postcond_name=postcond_name,
            unexpected_idx=unexpected_idx,
            test_type=self.UNDECIDABLE_PLAUSIBLE,
            test_proof=self.PLAUSIBLE_TEST_COMMAND,
            inverse=inverse,
            use_grind=use_grind,
        )

    def render_precond_formal_soundness(
        self,
        generated_precond: str,
        ground_truth_precond: str,
        proof: str,
    ) -> str:
        rendered = "example "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" :\n    ({ground_truth_precond}) → ({generated_precond}) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_precond_formal_unsoundness(
        self,
        generated_precond: str,
        ground_truth_precond: str,
        proof: str,
    ) -> str:
        rendered = "example :\n    ∃ "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" , ({ground_truth_precond}) ∧ (¬({generated_precond})) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_precond_formal_completeness(
        self, generated_precond: str, ground_truth_precond: str, proof: str
    ) -> str:
        rendered = "example "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" :\n    ({generated_precond}) → ({ground_truth_precond}) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_precond_formal_incompleteness(
        self, generated_precond: str, ground_truth_precond: str, proof: str
    ) -> str:
        rendered = "example :\n    ∃ "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" , ({generated_precond}) ∧ (¬({ground_truth_precond})) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_postcond_formal_soundness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        rendered = "example "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" :\n    (({ground_truth_precond}) ∧ ({generated_postcond})) → ({ground_truth_postcond}) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_postcond_formal_unsoundness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        rendered = "example :\n    ∃ "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" , (({ground_truth_precond}) ∧ ({generated_postcond})) ∧ (¬({ground_truth_postcond})) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_postcond_formal_completeness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        rendered = "example "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" :\n    (({ground_truth_precond}) ∧ ({ground_truth_postcond})) → ({generated_postcond}) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered

    def render_postcond_formal_incompleteness(
        self,
        ground_truth_precond: str,
        generated_postcond: str,
        ground_truth_postcond: str,
        proof: str,
    ) -> str:
        rendered = "example :\n    ∃ "
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" , (({ground_truth_precond}) ∧ ({ground_truth_postcond})) ∧ (¬({generated_postcond})) := by\n"
        rendered += self.render_lean_content(proof)
        return rendered


if __name__ == "__main__":
    signature = Signature(
        name="foo",
        parameters=[Parameter(param_name="x", param_type="Int")],
        return_type="Int",
    )
    template = LeanGenerationTaskTemplate(signature)
    precond = "True"
    code = "x + 1"
    spec = "result = x + 1"
    proof = "sorry"
    test_case = TestCase(input={"x": 1}, expected=2, unexpected=[3])

    rendered_precond = template.render_precond(precond)
    rendered_code = template.render_code(code)
    rendered_spec = template.render_postcond(spec, postcond_name="add_one")
    rendered_proof = template.render_proof(proof, postcond_name="add_one")
    rendered_code_unit_test = template.render_code_unit_test(test_case, test_idx=0)
    rendered_precond_unit_test_sound_decidable = (
        template.render_precond_unit_test_sound_decidable(test_case, test_idx=0)
    )
    rendered_precond_unit_test_sound_undecidable = (
        template.render_precond_unit_test_sound_plausible(
            test_case, test_idx=0, inverse=False
        )
    )
    rendered_spec_unit_test_complete_decidable = (
        template.render_postcond_unit_test_complete_decidable(
            test_case, postcond_name="add_one", test_idx=0
        )
    )
    rendered_spec_unit_test_complete_undecidable = (
        template.render_postcond_unit_test_complete_plausible(
            test_case, postcond_name="add_one", test_idx=0, inverse=False
        )
    )
    rendered_spec_unit_test_sound_decidable = (
        template.render_postcond_unit_test_sound_decidable(
            test_case, postcond_name="add_one", unexpected_idx=0, test_idx=0
        )
    )
    rendered_spec_unit_test_sound_undecidable = (
        template.render_postcond_unit_test_sound_plausible(
            test_case,
            postcond_name="add_one",
            unexpected_idx=0,
            test_idx=0,
            inverse=False,
        )
    )

    print(rendered_precond)
    print(rendered_code)
    print(rendered_spec)
    print(rendered_proof)
    print(rendered_code_unit_test)
    print(rendered_precond_unit_test_sound_decidable)
    print(rendered_precond_unit_test_sound_undecidable)
    print(rendered_spec_unit_test_complete_decidable)
    print(rendered_spec_unit_test_complete_undecidable)
    print(rendered_spec_unit_test_sound_decidable)
    print(rendered_spec_unit_test_sound_undecidable)
