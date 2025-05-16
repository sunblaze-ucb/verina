-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  -- !benchmark @start precond
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  -- !benchmark @start code
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  -- !benchmark @start postcond
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem swap_spec_satisfied (arr: Array Int) (i: Int) (j: Int) (h_precond : swap_precond (arr) (i) (j)) :
    swap_postcond (arr) (i) (j) (swap (arr) (i) (j) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold swap_postcond swap
  unfold swap_precond at h_precond
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h_precond

  apply And.intro
  . simp
    by_cases h_eq : (i = j)
    . rw [h_eq]
      rw [Array.getElem!_eq_getD]
      rw [Array.setIfInBounds]
      simp [h₄]
    . rw [Array.setIfInBounds_comm]
      let arr₁ := arr.setIfInBounds j.toNat arr[i.toNat]!
      have ha₁ : arr₁ = arr.setIfInBounds j.toNat arr[i.toNat]! := rfl
      let arr_j := arr[j.toNat]!
      have hi : arr_j = arr[j.toNat]! := rfl
      rw [←ha₁, ←hi]
      have h₃' : i.toNat < (arr₁.setIfInBounds i.toNat arr_j).size := by
        rw [ha₁]
        unfold Array.setIfInBounds
        split
        . simp
          split
          . simp
            exact h₃
          . simp
            exact h₃
        . split
          . simp
            exact h₃
          . simp
            exact h₃
      rw [Array.getElem!_eq_getD]
      unfold Array.getD
      split
      . simp
      . simp
      intro h
      have h_contr : i = j := by
        rw [← Int.toNat_of_nonneg h₁, ← Int.toNat_of_nonneg h₂]
        rw [h]
      contradiction
  . apply And.intro
    . simp
      by_cases h_eq : (i = j)
      . rw [h_eq]
        rw [Array.getElem!_eq_getD]
        rw [Array.setIfInBounds]
        simp [h₄]
      . let arr₁ := arr.setIfInBounds i.toNat arr[j.toNat]!
        have ha₁ : arr₁ = arr.setIfInBounds i.toNat arr[j.toNat]! := rfl
        let arr_i := arr[i.toNat]!
        have hi : arr_i = arr[i.toNat]! := rfl
        rw [←ha₁, ←hi]
        have h₃' : j.toNat < (arr₁.setIfInBounds j.toNat arr_i).size := by
          rw [ha₁]
          unfold Array.setIfInBounds
          split
          . simp
            split
            . simp
              exact h₄
            . simp
              exact h₄
          . split
            . simp
              exact h₄
            . simp
              exact h₄
        rw [Array.getElem!_eq_getD]
        unfold Array.getD
        split
        . simp
        . rename_i h
          contradiction
    . simp
      intro k hk hki hkj
      let arr₁ := (arr.setIfInBounds i.toNat arr[j.toNat]!)
      let harr₁ : arr₁ = (arr.setIfInBounds i.toNat arr[j.toNat]!) := rfl
      rw [←harr₁]
      have h₁ : arr₁[k]! = arr[k]! := by
        rw [Array.getElem!_eq_getD]
        rw [Array.getD]
        simp
        split
        . rw [Array.getElem_setIfInBounds_ne arr arr[j.toNat]! hk]
          rw [Array.getElem!_eq_getD]
          rw [Array.getD]
          simp
          split
          . rfl
          . rfl
          apply ne_comm.mp
          exact hki
        . rename_i h_contr
          rw [harr₁] at h_contr
          simp only [Array.size_setIfInBounds] at h_contr
          contradiction
      rw [Array.getElem!_eq_getD]
      rw [Array.getD]
      simp
      split
      . rw [Array.getElem_setIfInBounds_ne arr₁ arr[i.toNat]!]
        rw [←h₁]
        rw [Array.getElem!_eq_getD]
        rw [Array.getD]
        simp
        split
        . simp
        . simp
        rename_i h
        exact h
        rw [ne_comm]
        exact hkj
      . rename_i h_contr
        have h : arr.size = arr₁.size := by
          rw [harr₁]
          simp
        rw [←h] at h_contr
        contradiction
  -- !benchmark @end proof
