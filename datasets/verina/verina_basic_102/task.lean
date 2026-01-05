-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  -- !benchmark @start code
  let n := nums.size
  let rec outer (i : Nat) : Option (Nat × Nat) :=
    if i < n - 1 then
      let rec inner (j : Nat) : Option (Nat × Nat) :=
        if j < n then
          if nums[i]! + nums[j]! = target then
            some (i, j)
          else
            inner (j + 1)
        else
          none
      match inner (i + 1) with
      | some pair => some pair
      | none      => outer (i + 1)
    else
      none
  match outer 0 with
  | some pair => pair
  | none      => panic "twoSum: no solution found"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  -- !benchmark @start postcond
  let (i, j) := result
  -- Basic validity: i < j, in bounds, and sum equals target
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- Lexicographically first: no valid pair (i', j') with i' < i exists
  (nums.toList.take i).zipIdx.all (fun ⟨a, i'⟩ =>
    (nums.toList.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
  -- For our i, j is the smallest valid partner
  ((nums.toList.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem twoSum_spec_satisfied (nums: Array Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
