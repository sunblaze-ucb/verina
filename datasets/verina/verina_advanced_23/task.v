(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to compute integer power *)
Fixpoint pow (base : Z) (exp : nat) : Z :=
  match exp with
  | O => 1%Z
  | S n => (base * pow base n)%Z
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isPowerOfTwo_precond_dec (n : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition isPowerOfTwo_precond (n : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint aux (m : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if (m =? 1)%Z then true
      else if negb ((m mod 2)%Z =? 0)%Z then false
      else aux (m / 2)%Z fuel'
  end.
(* !benchmark @end code_aux *)

Definition isPowerOfTwo (n : Z) (h_precond : isPowerOfTwo_precond n) : bool :=
  (* !benchmark @start code *)
  if (n <=? 0)%Z then false
else aux n (Z.abs_nat n)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isPowerOfTwo_postcond_dec (n : Z) (result : bool) : bool :=
  result.
(* !benchmark @end postcond_aux *)

Definition isPowerOfTwo_postcond (n : Z) (result : bool) (h_precond : isPowerOfTwo_precond n) : Prop :=
  (* !benchmark @start postcond *)
  if result then exists (x : nat), (pow 2%Z x = n) /\ (n > 0)%Z
else ~ (exists (x : nat), (pow 2%Z x = n) /\ (n > 0)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPowerOfTwo_postcond_satisfied (n : Z) (h_precond : isPowerOfTwo_precond n) :
    isPowerOfTwo_postcond n (isPowerOfTwo n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
