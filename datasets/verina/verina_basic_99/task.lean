-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result = 3 * x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold Triple_postcond Triple
  simp
  split_ifs with h₁
  . rw [←Int.add_mul]
    simp
    have h : (6: ℤ) = 3 * 2 := by simp
    rw [h, Int.mul_comm, Int.mul_ediv_assoc, Int.mul_ediv_assoc]
    simp
    rw [Int.mul_comm]
    rfl
    simp
  . rw (occs := [1]) [←Int.one_mul x]
    rw [←Int.add_mul]
    simp
  -- !benchmark @end proof
