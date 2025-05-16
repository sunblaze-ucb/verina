-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  -- !benchmark @start postcond
  result = List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumOfDigits_spec_satisfied (n: Nat) (h_precond : sumOfDigits_precond (n)) :
    sumOfDigits_postcond (n) (sumOfDigits (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
