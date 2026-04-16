-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start task_aux
-- Lean 4's Float is an opaque C FFI type with no kernel lemmas.
-- These axioms capture IEEE 754-compliant behavior for non-NaN/non-Inf floats.
axiom Float.not_isNaN_ofNat (n : Nat) : (n.toFloat).isNaN = false
axiom Float.isFinite_ofNat (n : Nat) (h : n < 2 ^ 53) :
    (n.toFloat).isNaN = false ∧ (n.toFloat).isInf = false
axiom Float.ofNat_beq_zero_false (n : Nat) (h : 0 < n) :
    (n.toFloat == (0 : Float)) = false
axiom Float.beq_self_of_not_isNaN (x : Float) (h : x.isNaN = false) :
    (x == x) = true
axiom Float.not_isNaN_sub (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hx_inf : x.isInf = false) (hy_inf : y.isInf = false) :
    (x - y).isNaN = false
axiom Float.not_isNaN_div (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hy0 : (y == 0) = false) (hinf : x.isInf = false ∨ y.isInf = false) :
    (x / y).isNaN = false
axiom Float.le_total_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x ≤ y ∨ y ≤ x
axiom Float.lt_iff_le_not_le_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x
-- !benchmark @end task_aux

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧ n < 9007199254740992  -- n must be positive and bounded for Float precision
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  -- !benchmark @start code
  if n ≤ 0 then (0, 0.0)
  else
    let sum := (List.range (n + 1)).sum
    let average : Float := sum.toFloat / (n.toFloat)
    (sum, average)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  -- !benchmark @start postcond
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumAndAverage_spec_satisfied (n: Nat) (h_precond : sumAndAverage_precond (n)) :
    sumAndAverage_postcond (n) (sumAndAverage (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
