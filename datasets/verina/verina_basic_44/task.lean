-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  -- !benchmark @start code
  -- First create pairs of (index, value) for all elements in the array
  let indexedArray := a.mapIdx fun i x => (i, x)

  -- Check if all elements at odd indices are odd numbers
  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  -- !benchmark @start postcond
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isOddAtIndexOdd_spec_satisfied (a: Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    isOddAtIndexOdd_postcond (a) (isOddAtIndexOdd (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold isOddAtIndexOdd isOddAtIndexOdd_postcond
  simp_all
  constructor
  · intro h
    intro i hi h_odd
    -- Since the function returns true, all elements in satisfy the predicate
    have h_all_odd : (a.mapIdx (fun j x => (j, x))).all (fun (i, x) => !(isOdd i) || isOdd x) = true := by
      simp_all
    -- Apply the property of Array.all
    rw [Array.all_iff_forall] at h_all_odd
    simp_all
    have h_sat_i : !(isOdd i) || isOdd a[i] := by
      simp
      apply h_all_odd i hi
    simp [h_odd] at h_sat_i
    exact h_sat_i
  · intro h
    apply Array.all_iff_forall.mpr
    intro i hi
    simp
    intro hi'
    have h_sat : isOdd i → isOdd a[i] := by
      apply h i hi'
    rw [Decidable.imp_iff_not_or] at h_sat
    simp at h_sat
    exact h_sat
  -- !benchmark @end proof
