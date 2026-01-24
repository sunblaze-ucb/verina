(* !benchmark @start import type=task *)
Require Import String.
Require Import Ascii.
Require Import List.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition countDigits_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((nat_of_ascii "0"%char) <=? n)%nat && (n <=? (nat_of_ascii "9"%char))%nat.

Fixpoint countDigitsAux (l : list ascii) : nat :=
  match l with
  | [] => O
  | h :: t => if isDigit h then S (countDigitsAux t) else countDigitsAux t
  end.
(* !benchmark @end code_aux *)

Definition countDigits (s : string) : nat :=
  (* !benchmark @start code *)
  countDigitsAux (list_ascii_of_string s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isDigit_spec (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((nat_of_ascii "0"%char) <=? n)%nat && (n <=? (nat_of_ascii "9"%char))%nat.

Fixpoint countDigitsSpec (l : list ascii) : nat :=
  match l with
  | [] => O
  | h :: t => if isDigit_spec h then S (countDigitsSpec t) else countDigitsSpec t
  end.
(* !benchmark @end postcond_aux *)

Definition countDigits_postcond (s : string) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((result - countDigitsSpec (list_ascii_of_string s) =? 0)%nat && (countDigitsSpec (list_ascii_of_string s) - result =? 0)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem countDigits_postcond_satisfied (s : string) :
    countDigits_precond s = true ->
    countDigits_postcond s (countDigits s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
