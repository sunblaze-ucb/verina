-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  -- !benchmark @start code
  if a <= b then a else b
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (a: Int) (b: Int) (h_precond : myMin_precond (a) (b)) :
    myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold myMin myMin_postcond
  constructor
  · split
    case left.isTrue h =>
      simp
      exact h
    case left.isFalse h =>
      simp
      rw [Int.not_le] at h
      exact Int.le_of_lt h
  · split <;> simp
  -- !benchmark @end proof
