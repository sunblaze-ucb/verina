-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  -- !benchmark @start code
  let rec outer (lst : List Int) (i : Nat)
            : Option (Nat × Nat) :=
        match lst with
        | [] =>
            none
        | x :: xs =>
            let rec inner (lst' : List Int) (j : Nat)
                    : Option Nat :=
                match lst' with
                | [] =>
                    none
                | y :: ys =>
                    if x + y = target then
                        some j
                    else
                        inner ys (j + 1)
            match inner xs (i + 1) with
            | some j =>
                some (i, j)
            | none =>
                outer xs (i + 1)
        outer nums 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        -- Lexicographically first: no valid pair (i', j') with i' < i exists
        (nums.take i).zipIdx.all (fun ⟨a, i'⟩ =>
          (nums.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
        -- For this i, j is the smallest valid partner
        ((nums.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


