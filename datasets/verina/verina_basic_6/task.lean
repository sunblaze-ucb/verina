-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold minOfThree minOfThree_postcond

  split

  -- Case 1: a is the minimum
  · by_cases h1: a <= b && a <= c
    · constructor
      · simp_all
      · simp
    · contradiction

  split

  -- Case 2: b is the minimum
  · by_cases h2: b <= a && b <= c
    · constructor
      · simp_all
      · simp
    · contradiction

  -- Case 3: c is the minimum
  · by_cases h3: c < a && c < b
    · constructor
      · simp_all
        constructor
        · exact le_of_lt h3.1
        · exact le_of_lt h3.2
      · simp
    · constructor
      · simp_all
        by_cases h': a <= b
        · simp_all
          have h'': a <= c := by
            exact le_trans h' h3
          rw [← not_lt] at h''
          contradiction
        · simp_all
          have _: b <= a := by exact le_of_lt h'
          simp_all
          have h'': c < b := by assumption
          have h''': c < a := by exact lt_trans h'' h'
          apply h3 at h'''
          rw [← not_lt] at h'''
          contradiction
      · simp
  -- !benchmark @end proof
