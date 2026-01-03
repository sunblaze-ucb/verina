(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition letterCombinations_precond_dec (digits : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition letterCombinations_precond (digits : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition letterCombinations (digits : string) (h_precond : letterCombinations_precond digits) : (list string) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition letterCombinations_postcond_dec (digits : string) (result : (list string)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition letterCombinations_postcond (digits : string) (result : (list string)) (h_precond : letterCombinations_precond digits) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem letterCombinations_postcond_satisfied (digits : string) (h_precond : letterCombinations_precond digits) :
    letterCombinations_postcond digits (letterCombinations digits h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
