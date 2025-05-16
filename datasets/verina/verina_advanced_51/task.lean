-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b
  -- !benchmark @end precond


-- !benchmark @start code_aux
def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

-- !benchmark @end code_aux


def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  -- !benchmark @start code
  let merged := mergeSortedAux a b
  merged
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible, simp]
def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeSorted_spec_satisfied (a: List Int) (b: List Int) (h_precond : mergeSorted_precond (a) (b)) :
    mergeSorted_postcond (a) (b) (mergeSorted (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


