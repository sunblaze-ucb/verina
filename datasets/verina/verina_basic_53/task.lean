-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  -- !benchmark @start postcond
  result = N * (N + 1) / 2
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold CalSum_postcond CalSum
  induction N with
  | zero =>
    unfold CalSum.loop
    simp
  | succ n ih =>
    unfold CalSum_precond at ih
    simp at ih
    unfold CalSum.loop
    simp
    rw [ih]
    rw [Nat.add_comm, ←(@Nat.add_mul_div_left (n * (n + 1)) (n+1) (2))]
    rw [← Nat.add_mul, Nat.mul_comm]
    simp
  -- !benchmark @end proof
