(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import PeanoNat.
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

Definition allDigits_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char)).

Fixpoint allDigits_loop (chars : list ascii) : bool :=
  match chars with
  | [] => true
  | c :: rest => if isDigit c then allDigits_loop rest else false
  end.
(* !benchmark @end code_aux *)

Definition allDigits (s : string) : bool :=
  (* !benchmark @start code *)
  allDigits_loop (list_ascii_of_string s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isDigit_spec (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char)).
(* !benchmark @end postcond_aux *)

Definition allDigits_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb result (forallb isDigit_spec (list_ascii_of_string s))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allDigits_postcond_satisfied (s : string) :
    allDigits_precond s = true ->
    allDigits_postcond s (allDigits s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
