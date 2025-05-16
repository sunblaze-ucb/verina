-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)
-- !benchmark @end code_aux


def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  -- !benchmark @start code
  if y = 0 then (Int.ofNat x, 0) else divMod x y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  -- !benchmark @start postcond
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DivisionFunction_spec_satisfied (x: Nat) (y: Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    DivisionFunction_postcond (x) (y) (DivisionFunction (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold DivisionFunction_postcond DivisionFunction
  simp
  split
  {
    simp
    intro h₁
    contradiction
  }
  {

    have h_left : (¬y = 0 →
    (divMod x y).snd * ↑y + (divMod x y).fst = ↑x ∧
      (0 ≤ (divMod x y).fst ∧ (divMod x y).fst < ↑y) ∧ 0 ≤ (divMod x y).snd) := by
      intro h₁
      have h₁_left : (divMod x y).snd * ↑y + (divMod x y).fst = ↑x := by
        unfold divMod
        simp
        have h₁ := Int.ediv_add_emod' x y
        apply h₁
      have h₁_right : (0 ≤ (divMod x y).1 ∧ (divMod x y).1 < ↑y) ∧ 0 ≤ (divMod x y).2 := by
        have h₂_left : (0 ≤ (divMod x y).1 ∧ (divMod x y).1 < ↑y) := by
          have h₃_left : 0 ≤ (divMod x y).1 := by
            unfold divMod
            simp
            rw [←Int.natCast_mod, ←Int.ofNat_eq_natCast]
            have ha := Int.zero_le_ofNat (x % y)
            apply ha
          have h₃_right : (divMod x y).1 < ↑y := by
            unfold divMod
            simp
            rw [←Int.natCast_mod]
            have ha := @Int.natMod_lt x y h₁
            rw [Int.natMod, ←Int.natCast_mod, Int.toNat_ofNat] at ha
            rw [←Mathlib.Tactic.Zify.natCast_lt]
            apply ha
          exact ⟨h₃_left, h₃_right⟩

        have h₂_right : 0 ≤ (divMod x y).2 := by
          unfold divMod
          simp
          rw [←Int.natCast_div]
          have ha := Int.natCast_nonneg (x / y)
          apply ha
        exact ⟨h₂_left, h₂_right⟩
      exact ⟨h₁_left, h₁_right⟩
    have h_right : (y = 0 → (divMod x y).fst = ↑x ∧ (divMod x y).snd = 0) := by
      intro h₀
      have h₁_left : (divMod x y).1 = ↑x := by
        unfold divMod
        simp
        rw [←Int.natCast_mod, h₀, Nat.mod_zero]
      have h₁_right : (divMod x y).snd = 0 := by
        unfold divMod
        simp
        rw [←Int.natCast_div, h₀, Nat.div_zero, ←@Int.cast_id 0]
        rfl
      exact ⟨h₁_left, h₁_right⟩
    constructor
    · simp_all [h_left]
    · simp_all [h_right]
  }
  -- !benchmark @end proof
