-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  -- !benchmark @start code
  let a := 2 * x
  let b := 2 * a
  (a, b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  -- !benchmark @start postcond
  result.fst = 2 * x ∧ result.snd = 4 * x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
