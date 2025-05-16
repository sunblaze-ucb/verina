-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold LinearSearch_postcond LinearSearch
  apply And.intro
  . let aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → LinearSearch.loop a e x ≤ a.size := by
      intro hx₀ hx₁
      let nx := a.size - x
      have hn₁ : nx = a.size - x := by rfl
      have hn₂ : x = a.size - nx := by
        rw [hn₁, Nat.sub_sub_self]
        apply hx₁
      rw [hn₂]
      induction nx with
      | zero =>
        unfold LinearSearch.loop
        simp
      | succ n₁ ih =>
        by_cases hp : (a.size ≤ n₁)
        . rw [Nat.sub_eq_zero_of_le hp] at ih
          have h_tmp : a.size ≤ n₁ + 1 := Nat.le_add_right_of_le hp
          rw [Nat.sub_eq_zero_of_le h_tmp]
          exact ih
        . have hq : n₁ < a.size := Nat.not_le.mp hp
          unfold LinearSearch.loop
          simp
          split_ifs
          . simp
          . rw [Nat.sub_add_eq, Nat.sub_add_cancel]
            exact ih
            apply Nat.zero_lt_sub_of_lt
            exact hq
          simp
    have h₀ : 0 ≤ a.size := by simp
    have h_triv : 0 ≤ 0 := by simp
    exact aux 0 h_triv h₀
  . apply And.intro
    . let aux (x : Nat) : (x ≥ 0) → (x ≤ a.size) → LinearSearch.loop a e x = a.size ∨ a[LinearSearch.loop a e x]! = e := by
        intro hx₀ hx₁
        let nx := a.size - x
        have hn₁ : nx = a.size - x := by rfl
        have hn₂ : x = a.size - nx := by
          rw [hn₁, Nat.sub_sub_self]
          apply hx₁
        rw [hn₂]
        induction nx with
        | zero =>
          unfold LinearSearch.loop
          simp
        | succ n₁ ih =>
          -- Ohh boy...
          by_cases hp : (a.size ≤ n₁)
          . rw [Nat.sub_eq_zero_of_le hp] at ih
            have h_tmp : a.size ≤ n₁ + 1 := Nat.le_add_right_of_le hp
            rw [Nat.sub_eq_zero_of_le h_tmp]
            exact ih
          . have hq : n₁ < a.size := Nat.not_le.mp hp
            apply Or.elim ih -- Didn't find elem, so we're gonna also return a.size...
            . intro ih₁
              unfold LinearSearch.loop
              split_ifs
              . rename_i h₁ h₂
                rw [h₂]
                simp
              . rename_i ha₁ ha₂
                rw [Nat.sub_add_eq, Nat.sub_add_cancel]
                rw [ih₁]
                simp
                apply Nat.zero_lt_sub_of_lt
                exact hq
              . rename_i h₁
                have ha₁ := Nat.not_lt.mp h₁
                have ha₂ := Nat.sub_le a.size (n₁ + 1)
                have ha := Nat.eq_iff_le_and_ge.mpr ⟨ha₁, ha₂⟩
                rw [←ha]
                simp
            . intro ih₂
              unfold LinearSearch.loop
              split_ifs
              . rename_i h₁ h₂
                rw [h₂]
                simp
              . rename_i ha₁ ha₂
                rw [Nat.sub_add_eq, Nat.sub_add_cancel]
                rw [ih₂]
                simp
                apply Nat.zero_lt_sub_of_lt
                exact hq
              . rename_i h₁
                have ha₁ := Nat.not_lt.mp h₁
                have ha₂ := Nat.sub_le a.size (n₁ + 1)
                have ha := Nat.eq_iff_le_and_ge.mpr ⟨ha₁, ha₂⟩
                rw [←ha]
                simp
      have h₀ : 0 ≤ 0 := by simp
      have h₁ : 0 ≤ a.size := by simp
      exact aux 0 h₀ h₁
    . let aux (x : Nat) : (0 ≤ x) → (x ≤ a.size) → (∀ i, x ≤ i → i < LinearSearch.loop a e x → a[i]! ≠ e) := by
        intro hx₀ hx₁ i
        let nx := a.size - x
        have hn₁ : nx = a.size - x := by rfl
        have hn₂ : x = a.size - nx := by
          rw [hn₁, Nat.sub_sub_self]
          apply hx₁
        rw [hn₂]
        induction nx with
        | zero =>
          -- There's no such i
          unfold LinearSearch.loop
          simp
          intro hxi hi
          have h_contr := Nat.lt_of_le_of_lt hxi hi
          have h : a.size ≤ a.size := by simp
          have h : a.size - a.size < a.size - a.size := Nat.sub_lt_sub_right h h_contr
          simp at h
        | succ n ih =>
          intro hxi
          unfold LinearSearch.loop
          simp
          split_ifs
          . rename_i h₁ h₂
            intro h_contr
            have h := Nat.lt_of_le_of_lt hxi h_contr
            simp at h
          . rename_i h₁ h₂
            by_cases hp : (a.size ≤ n)
            . rw [Nat.sub_eq_zero_iff_le.mpr hp] at ih
              intro hi
              have hp₁ : a.size ≤ n + 1 := by
                have h₁' : n ≤ n + 1 := by simp
                exact Nat.le_trans hp h₁'
              rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at hxi
              rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at hi
              rw [Nat.sub_eq_zero_iff_le.mpr hp₁] at h₂
              have ih₁ := ih hxi
              simp at hi
              unfold LinearSearch.loop at ih₁
              split_ifs at ih₁
              . rename_i h₁'
                simp at ih₁
                exact ih₁ hi
              . rename_i h₁'
                contradiction
            . have hq : n < a.size := Nat.not_le.mp hp
              have hq' : 1 ≤ a.size - n := by
                have h : 0 < a.size - n := by
                  exact Nat.sub_pos_of_lt hq
                exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt h)
              rw [Nat.sub_add_eq, Nat.sub_add_cancel hq']
              intro hi
              by_cases h_bounds : (a.size - n ≤ i)
              . exact ih h_bounds hi
              . have h_bounds' : ( i + 1 < a.size - n + 1) := (@Nat.add_lt_add_iff_right 1 i (a.size - n)).mpr (Nat.not_le.mp h_bounds)
                have h := Nat.le_of_lt_add_one h_bounds'
                apply Nat.le_sub_of_add_le at h
                rw [← Nat.sub_add_eq] at h
                have hi_fixed := Nat.eq_iff_le_and_ge.mpr ⟨hxi, h⟩
                rw [hi_fixed] at h₂
                exact h₂
          . intro h_contr
            have h := Nat.lt_of_le_of_lt hxi h_contr
            simp at h
      have h₀ : 0 ≤ a.size := by simp
      have h_triv : 0 ≤ 0 := by simp
      intro i
      have h_tmp : 0 ≤ i := Nat.zero_le i
      exact aux 0 h_triv h₀ i h_tmp


  -- !benchmark @end proof
