(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Nat.

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii "0"%char in
  let nine := nat_of_ascii "9"%char in
  andb (Nat.leb zero n) (Nat.leb n nine).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition countDigits_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition countDigits_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_of_string s'
  end.
(* !benchmark @end code_aux *)

Definition countDigits (s : string) (h_precond : countDigits_precond s) : nat :=
  (* !benchmark @start code *)
  length (filter isDigit (list_of_string s))
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition countDigits_postcond_dec (s : string) (result : nat) : bool :=
  let expected := length (filter isDigit (list_of_string s)) in
  andb (Nat.eqb (result - expected) 0%nat) (Nat.eqb (expected - result) 0%nat).
(* !benchmark @end postcond_aux *)

Definition countDigits_postcond (s : string) (result : nat) (h_precond : countDigits_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (result - length (filter isDigit (list_of_string s)) = 0%nat) /\
(length (filter isDigit (list_of_string s)) - result = 0%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem countDigits_postcond_satisfied (s : string) (h_precond : countDigits_precond s) :
    countDigits_postcond s (countDigits s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
