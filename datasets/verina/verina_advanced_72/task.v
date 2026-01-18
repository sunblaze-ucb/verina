(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional helper definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition singleDigitPrimeFactor_precond_dec (n : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition singleDigitPrimeFactor_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No helper functions needed *)
(* !benchmark @end code_aux *)

Definition singleDigitPrimeFactor (n : nat) (h_precond : singleDigitPrimeFactor_precond n) : nat :=
  (* !benchmark @start code *)
  if Nat.eqb n 0%nat then 0%nat
else if Nat.eqb (Nat.modulo n 2%nat) 0%nat then 2%nat
else if Nat.eqb (Nat.modulo n 3%nat) 0%nat then 3%nat
else if Nat.eqb (Nat.modulo n 5%nat) 0%nat then 5%nat
else if Nat.eqb (Nat.modulo n 7%nat) 0%nat then 7%nat
else 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition singleDigitPrimeFactor_postcond_dec (n : nat) (result : nat) : bool :=
  (* result ∈ [0, 2, 3, 5, 7] *)
  match result with
  | 0%nat => true
  | 2%nat => true
  | 3%nat => true
  | 5%nat => true
  | 7%nat => true
  | _ => false
  end &&
  (* if result = 0 then (n = 0 ∨ all primes don't divide n) *)
  (if Nat.eqb result 0%nat then
     Nat.eqb n 0%nat ||
     (negb (Nat.eqb (Nat.modulo n 2%nat) 0%nat) &&
      negb (Nat.eqb (Nat.modulo n 3%nat) 0%nat) &&
      negb (Nat.eqb (Nat.modulo n 5%nat) 0%nat) &&
      negb (Nat.eqb (Nat.modulo n 7%nat) 0%nat))
   else true) &&
  (* if result ≠ 0 then n ≠ 0 ∧ n % result = 0 ∧ smaller primes don't divide *)
  (if negb (Nat.eqb result 0%nat) then
     negb (Nat.eqb n 0%nat) &&
     Nat.eqb (Nat.modulo n result) 0%nat &&
     match result with
     | 2%nat => true
     | 3%nat => negb (Nat.eqb (Nat.modulo n 2%nat) 0%nat)
     | 5%nat => negb (Nat.eqb (Nat.modulo n 2%nat) 0%nat) &&
                negb (Nat.eqb (Nat.modulo n 3%nat) 0%nat)
     | 7%nat => negb (Nat.eqb (Nat.modulo n 2%nat) 0%nat) &&
                negb (Nat.eqb (Nat.modulo n 3%nat) 0%nat) &&
                negb (Nat.eqb (Nat.modulo n 5%nat) 0%nat)
     | _ => true
     end
   else true).
(* !benchmark @end postcond_aux *)

Definition singleDigitPrimeFactor_postcond (n : nat) (result : nat) (h_precond : singleDigitPrimeFactor_precond n) : Prop :=
  (* !benchmark @start postcond *)
  In result [0%nat; 2%nat; 3%nat; 5%nat; 7%nat] /\
(result = 0%nat -> (n = 0%nat \/ (Nat.modulo n 2%nat <> 0%nat /\ Nat.modulo n 3%nat <> 0%nat /\ Nat.modulo n 5%nat <> 0%nat /\ Nat.modulo n 7%nat <> 0%nat))) /\
(result <> 0%nat -> n <> 0%nat /\ Nat.modulo n result = 0%nat /\
  (forall x, In x [2%nat; 3%nat; 5%nat; 7%nat] -> x < result -> Nat.modulo n x <> 0%nat))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem singleDigitPrimeFactor_postcond_satisfied (n : nat) (h_precond : singleDigitPrimeFactor_precond n) :
    singleDigitPrimeFactor_postcond n (singleDigitPrimeFactor n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
