(* Coq version of isPrime benchmark task *)
(* Determines if a natural number is prime *)

Require Import ZArith.
Require Import Arith.
Require Import Bool.
Require Import Lia.
Open Scope nat_scope.

(* !benchmark @start import type=task *)
(* Task-level imports *)
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* Solution-specific imports *)
(* !benchmark @end import *)

(* !benchmark @start solution_aux *)
(* Helper: check if any number from 2 to k-1 divides n *)
Fixpoint has_divisor_in_range (n k : nat) : bool :=
  match k with
  | 0 => false
  | 1 => false
  | S k' =>
      if Nat.eqb k' 0 then false
      else if Nat.eqb k' 1 then false
      else if Nat.eqb (n mod k') 0 then true
      else has_divisor_in_range n k'
  end.

(* Check primality: n >= 2 and no divisor in [2, n-1] *)
Definition is_prime_check (n : nat) : bool :=
  if Nat.ltb n 2 then false
  else negb (has_divisor_in_range n n).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* !benchmark @end precond_aux *)

Definition isPrime_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  n >= 2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isPrime (n : nat) (h_precond : isPrime_precond n) : bool :=
  (* !benchmark @start code *)
  is_prime_check n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Formal definition of prime for specification *)
Definition is_prime_prop (n : nat) : Prop :=
  n >= 2 /\ forall k, 2 <= k < n -> n mod k <> 0.
(* !benchmark @end postcond_aux *)

Definition isPrime_postcond (n : nat) (result : bool) (h_precond : isPrime_precond n) : Prop :=
  (* !benchmark @start postcond *)
  (result = true <-> is_prime_prop n)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

(* Note: Full formal proof of isPrime correctness is complex *)
(* For benchmarking, we rely on unit tests *)
