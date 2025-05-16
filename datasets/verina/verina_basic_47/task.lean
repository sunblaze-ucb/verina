-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  -- !benchmark @start code
  a.toList.sum
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!
-- !benchmark @end postcond_aux


@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  -- !benchmark @start postcond
  result = sumTo a a.size
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem arraySum_spec_satisfied (a: Array Int) (h_precond : arraySum_precond (a)) :
    arraySum_postcond (a) (arraySum (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold arraySum arraySum_postcond
  cases a with | mk d =>
    induction d with
    | nil => simp [sumTo]
    | cons x xs ih =>
      simp [ih]

      have h1 : sumTo ⟨x::xs⟩ (xs.length + 1) = sumTo ⟨x::xs⟩ xs.length + (x::xs)[xs.length] := by
        rw [sumTo]
        simp

      rw [h1]

      have h2 : xs = List.nil → (x::xs)[xs.length] = x := by
        intro h_nil
        simp [h_nil]

      have h3 (x' : Int) (xs' : List Int): xs'.length ≠ 0 → sumTo ⟨x'::xs'⟩ xs'.length = x' + sumTo ⟨xs'⟩ (xs'.length - 1) := by
        induction xs'.length with
        | zero => simp
        | succ n ih_len =>
          simp
          cases n with
          | zero => simp [sumTo]
          | succ n' =>
            simp at ih_len
            unfold sumTo
            simp_all
            rw [Int.add_assoc]

      cases xs with
      | nil => simp [h2, sumTo]
      | cons y ys =>
        simp_all
        have h4 : sumTo ⟨x::y::ys⟩ (ys.length + 1) = x + sumTo ⟨y::ys⟩ ys.length := by
          apply h3 x (y::ys)
          simp
        rw [h4, sumTo]
        simp
        rw [Int.add_assoc]
  -- !benchmark @end proof
