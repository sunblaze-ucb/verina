-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux
def mergeLoop (a1 a2 : Array Nat) (i j : Nat) (result : Array Nat) : Nat × Nat × Array Nat :=
  if h : i < a1.size ∧ j < a2.size then
    if a1[i]! ≤ a2[j]! then
      mergeLoop a1 a2 (i + 1) j (result.push a1[i]!)
    else
      mergeLoop a1 a2 i (j + 1) (result.push a2[j]!)
  else
    (i, j, result)
termination_by a1.size - i + (a2.size - j)

def drain (arr : Array Nat) (i : Nat) (result : Array Nat) : Array Nat :=
  if h : i < arr.size then
    drain arr (i + 1) (result.push arr[i]!)
  else
    result
termination_by arr.size - i
-- !benchmark @end code_aux


def mergeSorted (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Array Nat :=
  -- !benchmark @start code
  let (i, j, result) := mergeLoop a1 a2 0 0 #[]
  let result := drain a1 i result
  let result := drain a2 j result
  result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeSorted_spec_satisfied (a1: Array Nat) (a2: Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    mergeSorted_postcond (a1) (a2) (mergeSorted (a1) (a2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


