-- !benchmark @start import type=solution
import Mathlib.Data.Nat.Prime.Defs
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧
  primes.length > 0 ∧
  primes.all (fun p => Nat.Prime p) ∧
  List.Nodup primes
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  -- !benchmark @start code
  let rec countFactors (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
    match primes with
    | [] => []
    | p :: ps =>
      let (count, n') :=
        countFactor n p 0
      (p, count) :: countFactors n' ps

  countFactors n primes
  where

  countFactor : Nat → Nat → Nat → Nat × Nat
  | 0, _, count =>
    (count, 0)
  | n, p, count =>
    if h : n > 0 ∧ p > 1 then
      have : n / p < n :=
        Nat.div_lt_self h.1 h.2
      if n % p == 0 then
        countFactor (n / p) p (count + 1)
      else
        (count, n)
    else
      (count, n)
  termination_by n _ _ => n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  -- !benchmark @start postcond
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findExponents_spec_satisfied (n: Nat) (primes: List Nat) (h_precond : findExponents_precond (n) (primes)) :
    findExponents_postcond (n) (primes) (findExponents (n) (primes) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof


