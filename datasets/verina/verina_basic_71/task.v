(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition LongestCommonPrefix_precond_dec (str1 : (list ascii)) (str2 : (list ascii)) : bool := true.
(* !benchmark @end precond_aux *)

Definition LongestCommonPrefix_precond (str1 : (list ascii)) (str2 : (list ascii)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition LongestCommonPrefix (str1 : (list ascii)) (str2 : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) : (list ascii) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LongestCommonPrefix_postcond_dec (str1 : (list ascii)) (str2 : (list ascii)) (result : (list ascii)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition LongestCommonPrefix_postcond (str1 : (list ascii)) (str2 : (list ascii)) (result : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem LongestCommonPrefix_postcond_satisfied (str1 : (list ascii)) (str2 : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) :
    LongestCommonPrefix_postcond str1 str2 (LongestCommonPrefix str1 str2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
