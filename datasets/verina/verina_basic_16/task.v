(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition replaceChars_precond_dec (s : string) (oldChar : ascii) (newChar : ascii) : bool := true.
(* !benchmark @end precond_aux *)

Definition replaceChars_precond (s : string) (oldChar : ascii) (newChar : ascii) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition replaceChars (s : string) (oldChar : ascii) (newChar : ascii) (h_precond : replaceChars_precond s oldChar newChar) : string :=
  (* !benchmark @start code *)
  ""
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition replaceChars_postcond_dec (s : string) (oldChar : ascii) (newChar : ascii) (result : string) : bool := true.
(* !benchmark @end postcond_aux *)

Definition replaceChars_postcond (s : string) (oldChar : ascii) (newChar : ascii) (result : string) (h_precond : replaceChars_precond s oldChar newChar) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem replaceChars_postcond_satisfied (s : string) (oldChar : ascii) (newChar : ascii) (h_precond : replaceChars_precond s oldChar newChar) :
    replaceChars_postcond s oldChar newChar (replaceChars s oldChar newChar h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
