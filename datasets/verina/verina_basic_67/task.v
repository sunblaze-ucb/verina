(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import Bool.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition IsPalindrome_precond_dec (x : (list ascii)) : bool := true.
(* !benchmark @end precond_aux *)

Definition IsPalindrome_precond (x : (list ascii)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition IsPalindrome (x : (list ascii)) (h_precond : IsPalindrome_precond x) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition IsPalindrome_postcond_dec (x : (list ascii)) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition IsPalindrome_postcond (x : (list ascii)) (result : bool) (h_precond : IsPalindrome_precond x) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem IsPalindrome_postcond_satisfied (x : (list ascii)) (h_precond : IsPalindrome_precond x) :
    IsPalindrome_postcond x (IsPalindrome x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
