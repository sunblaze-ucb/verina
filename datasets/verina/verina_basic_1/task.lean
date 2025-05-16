-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  a * b < 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold hasOppositeSign hasOppositeSign_postcond
  constructor

  · intro h
    cases h with
    | inl h1 =>
      simp
      have ⟨ha, hb⟩ := h1
      exact Int.mul_neg_of_neg_of_pos ha hb
    | inr h2 =>
      simp
      have ⟨ha, hb⟩ := h2
      rw [Int.mul_comm]
      exact Int.mul_neg_of_neg_of_pos hb ha

  · intro h
    simp at h
    cases a with
    | ofNat na =>
      simp
      cases na with
      | zero => simp [*] at h
      | succ na =>
        have ha : Int.ofNat (na + 1) > 0 := by simp
        have hb : b < 0 := (pos_iff_neg_of_mul_neg h).mp ha
        right
        simp_all
    | negSucc na =>
      have ha : Int.negSucc na < 0 := Int.negSucc_lt_zero na
      have hb : b > 0 := (neg_iff_pos_of_mul_neg h).mp ha
      simp_all
  -- !benchmark @end proof
