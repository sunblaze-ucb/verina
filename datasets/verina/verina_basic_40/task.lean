-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!  -- at least two distinct values
  -- !benchmark @end precond


-- !benchmark @start code_aux
def secondSmallestAux (s : Array Int) (i minIdx : Nat) (secondIdx : Option Nat) : Int :=
  if i ≥ s.size then
    match secondIdx with
    | some si => s[si]!
    | none => panic! "no second smallest"  -- unreachable given precondition
  else
    let x := s[i]!
    let m := s[minIdx]!
    match secondIdx with
    | none =>
      if x < m then
        secondSmallestAux s (i + 1) i (some minIdx)
      else if x > m then
        secondSmallestAux s (i + 1) minIdx (some i)
      else
        secondSmallestAux s (i + 1) minIdx none
    | some si =>
      let smin := s[si]!
      if x < m then
        secondSmallestAux s (i + 1) i (some minIdx)
      else if x < smin ∧ x > m then
        secondSmallestAux s (i + 1) minIdx (some i)
      else
        secondSmallestAux s (i + 1) minIdx (some si)
termination_by s.size - i
-- !benchmark @end code_aux


def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  -- !benchmark @start code
  secondSmallestAux s 1 0 none
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  -- !benchmark @start postcond
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem secondSmallest_spec_satisfied (s: Array Int) (h_precond : secondSmallest_precond (s)) :
    secondSmallest_postcond (s) (secondSmallest (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
