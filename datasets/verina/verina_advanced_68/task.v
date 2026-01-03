(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition runLengthEncoder_precond_dec (input : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition runLengthEncoder_precond (input : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition runLengthEncoder (input : string) (h_precond : runLengthEncoder_precond input) : string :=
  (* !benchmark @start code *)
  ""
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition runLengthEncoder_postcond_dec (input : string) (result : string) : bool := true.
(* !benchmark @end postcond_aux *)

Definition runLengthEncoder_postcond (input : string) (result : string) (h_precond : runLengthEncoder_precond input) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem runLengthEncoder_postcond_satisfied (input : string) (h_precond : runLengthEncoder_precond input) :
    runLengthEncoder_postcond input (runLengthEncoder input h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
