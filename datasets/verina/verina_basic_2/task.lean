-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findSmallest_precond (s : Array Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  -- !benchmark @start code
  s.toList.min?
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  -- !benchmark @start postcond
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findSmallest_spec_satisfied (s: Array Nat) (h_precond : findSmallest_precond (s)) :
    findSmallest_postcond (s) (findSmallest (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findSmallest_postcond findSmallest
  cases res : s.toList.min? with
  | none =>
    simp only [res]
    rw [List.min?_eq_none_iff] at res
    exact res
  | some r =>
    simp only [res]
    rw [List.min?_eq_some_iff'] at res
    exact res
  -- !benchmark @end proof
