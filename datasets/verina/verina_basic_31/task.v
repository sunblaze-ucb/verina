(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition toUppercase_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition toUppercase_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition toUppercase (s : string) (h_precond : toUppercase_precond s) : string :=
  (* !benchmark @start code *)
  ""
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition toUppercase_postcond_dec (s : string) (result : string) : bool := true.
(* !benchmark @end postcond_aux *)

Definition toUppercase_postcond (s : string) (result : string) (h_precond : toUppercase_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem toUppercase_postcond_satisfied (s : string) (h_precond : toUppercase_precond s) :
    toUppercase_postcond s (toUppercase s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
