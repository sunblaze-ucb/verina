-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 0 then -x else x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  -- !benchmark @start postcond
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  -- !benchmark @start proof
    simp [Abs_postcond, Abs]
    apply And.intro
    . intro h
      split
      case isTrue ht =>
        have h': ¬0 ≤ x := not_le.mpr ht
        contradiction
      case isFalse =>
        rfl
    . intro h
      split
      case isTrue =>
        simp
      case isFalse =>
        contradiction
  -- !benchmark @end proof
