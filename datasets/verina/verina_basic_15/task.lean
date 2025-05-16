-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  -- !benchmark @start postcond
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem containsConsecutiveNumbers_spec_satisfied (a: Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    containsConsecutiveNumbers_postcond (a) (containsConsecutiveNumbers (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold containsConsecutiveNumbers containsConsecutiveNumbers_postcond
  constructor
  · simp_all
    intro i hi hconsec
    have hi' : 1 + i < a.size := by
        rw [Nat.add_comm]
        exact Nat.add_lt_of_lt_sub hi
    have hi'' : i < a.size := by
      have : i < 1 + i := by
        simp [Nat.lt_add_of_pos_left]
      exact Nat.lt_trans this hi'
    constructor
    · exact Nat.lt_of_add_right_lt hi'
    · apply Array.any_iff_exists.mpr
      simp
      exists i
      simp [hi, hi'']
      have : a[i]! = a[i] := by
        exact getElem!_pos a i hi''
      rw [←this]
      exact hconsec
  · simp
    intro ha h
    have h' := Array.any_iff_exists.mp h
    simp at h'
    rcases h' with ⟨i, hi, ⟨hi', hconsec⟩⟩
    have : a[i]! = a[i] := by
      exact getElem!_pos a i hi
    exists i
    rw [this]
    simp_all
  -- !benchmark @end proof
