-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ nums.eraseDups.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  -- !benchmark @start code
  -- Build frequency list maintaining first occurrence order (deterministic)
  let freqList : List (Int × Nat) :=
    nums.foldl (init := []) fun acc n =>
      match acc.find? (fun (key, _) => key == n) with
      | some _ => acc.map (fun (key, cnt) => if key == n then (key, cnt + 1) else (key, cnt))
      | none => acc ++ [(n, 1)]
  -- Sort by frequency (descending), stable sort preserves first-occurrence order for ties
  let sorted := freqList.foldl
    (fun acc pair =>
      let (x, cx) := pair
      let rec insertSorted (xs : List (Int × Nat)) : List (Int × Nat) :=
        match xs with
        | [] => [pair]
        | (y, cy) :: ys =>
          if cx > cy then
            pair :: (y, cy) :: ys
          else
            (y, cy) :: insertSorted ys
      insertSorted acc
    ) []

  sorted.take k |>.map (fun (n, _) => n)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal (simplified: no tie-breaking constraint on ordering)
  (result.all (fun x =>
    nums.all (fun y =>
      y ∈ result ∨ nums.count x ≥ nums.count y
    ))) ∧

  -- Elements in result are ordered by non-increasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x ≥ nums.count y
  ) result.zipIdx
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem topKFrequent_spec_satisfied (nums: List Int) (k: Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    topKFrequent_postcond (nums) (k) (topKFrequent (nums) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


