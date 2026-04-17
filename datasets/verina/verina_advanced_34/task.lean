-- !benchmark @start import type=solution
import Mathlib.Data.List.Basic
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def binarySearchLeft (sub : Array Int) (num : Int) (left right : Nat) : Nat :=
  if h : left < right then
    let mid := (left + right) / 2
    if sub[mid]! == num then
      binarySearchLeft sub num left mid
    else if sub[mid]! < num then
      binarySearchLeft sub num (mid + 1) right
    else
      binarySearchLeft sub num left mid
  else
    left
termination_by right - left
-- !benchmark @end code_aux


def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  -- !benchmark @start code
  Id.run do
    if nums.isEmpty then return 0
    let mut sub : Array Int := Array.empty
    sub := sub.push nums.head!
    for num in nums.tail do
      if num > sub[sub.size - 1]! then
        sub := sub.push num
      else
        let left := binarySearchLeft sub num 0 (sub.size - 1)
        sub := sub.set! left num
    return Int.ofNat sub.size
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


