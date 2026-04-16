-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  -- !benchmark @start code
  -- scan for increasing triplet using Option for second to handle "not found yet"
  let rec loop (xs : List Int) (first : Int) (secondOpt : Option Int) : Bool :=
    match xs with
    | [] => false
    | x :: rest =>
      if x ≤ first then
        loop rest x secondOpt
      else
        match secondOpt with
        | none => loop rest first (some x)
        | some second =>
          if x ≤ second then
            loop rest first (some x)
          else
            true  -- found triplet
  match nums with
  | [] => false
  | x :: rest => loop rest x none
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem increasingTriplet_spec_satisfied (nums: List Int) (h_precond : increasingTriplet_precond (nums)) :
    increasingTriplet_postcond (nums) (increasingTriplet (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
