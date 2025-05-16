-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k < s.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  -- !benchmark @start code
  s.eraseIdx! k
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  -- !benchmark @start postcond
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold removeElement removeElement_postcond
  unfold removeElement_precond at h_precond
  simp_all
  unfold Array.eraseIdx!
  simp [h_precond]
  constructor
  · intro i hi
    have hi' : i < s.size - 1 := by
      have hk := Nat.le_sub_one_of_lt h_precond
      exact Nat.lt_of_lt_of_le hi hk
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
    unfold Array.getD
    simp [hi', Nat.lt_trans hi h_precond, Array.getElem_eraseIdx, hi]
  · intro i hi hi'
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
    unfold Array.getD
    have hi'' : i + 1 < s.size := by exact Nat.add_lt_of_lt_sub hi
    simp [hi, hi'']
    have : ¬ i < k := by simp [hi']
    simp [Array.getElem_eraseIdx, this]
  -- !benchmark @end proof
