-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Option Int :=
  -- !benchmark @start code
  let rec helper (seen : List Int) (rem : List Int) : Option Int :=
    match rem with
    | [] => none
    | h :: t => if seen.contains h then some h else helper (h :: seen) t
  helper [] lst
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Option Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  match result with
  | none => List.Nodup lst
  | some x =>
    lst.count x > 1 ∧
    (lst.filter (fun y => lst.count y > 1)).head? = some x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem firstDuplicate_spec_satisfied (lst: List Int) (h_precond : firstDuplicate_precond (lst)) :
    firstDuplicate_postcond (lst) (firstDuplicate (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


