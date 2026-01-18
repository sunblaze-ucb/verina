(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to check if a character is a digit *)
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii "0"%char in
  let nine := nat_of_ascii "9"%char in
  (Nat.leb zero n && Nat.leb n nine)%bool.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition allDigits_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition allDigits_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to check all characters in a string *)
Fixpoint allDigits_aux (l : list ascii) : bool :=
  match l with
  | [] => true
  | c :: rest => 
      if isDigit c then allDigits_aux rest else false
  end.
(* !benchmark @end code_aux *)

Definition allDigits (s : string) (h_precond : allDigits_precond s) : bool :=
  (* !benchmark @start code *)
  allDigits_aux (list_ascii_of_string s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition allDigits_postcond_dec (s : string) (result : bool) : bool :=
  let chars := list_ascii_of_string s in
  let all_are_digits := forallb isDigit chars in
  Bool.eqb result all_are_digits.
(* !benchmark @end postcond_aux *)

Definition allDigits_postcond (s : string) (result : bool) (h_precond : allDigits_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (result = true <-> forall c, In c (list_ascii_of_string s) -> isDigit c = true)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allDigits_postcond_satisfied (s : string) (h_precond : allDigits_precond s) :
    allDigits_postcond s (allDigits s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
