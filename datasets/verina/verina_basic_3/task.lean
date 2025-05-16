-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  n % 11 == 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  -- !benchmark @start postcond
  (∃ k : Int, n = 11 * k) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isDivisibleBy11_spec_satisfied (n: Int) (h_precond : isDivisibleBy11_precond (n)) :
    isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold isDivisibleBy11 isDivisibleBy11_postcond
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp
  · intro h
    exists n / 11
    rw [beq_iff_eq] at h
    refine Eq.symm (Int.mul_ediv_cancel_of_emod_eq_zero ?_)
    exact h
  -- !benchmark @end proof
