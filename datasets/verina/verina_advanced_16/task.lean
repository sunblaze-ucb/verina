-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
  -- !benchmark @start code
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


