(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition smallestMissing_precond_dec (l : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition smallestMissing_precond (l : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition smallestMissing (l : (list nat)) (h_precond : smallestMissing_precond l) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition smallestMissing_postcond_dec (l : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition smallestMissing_postcond (l : (list nat)) (result : nat) (h_precond : smallestMissing_precond l) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem smallestMissing_postcond_satisfied (l : (list nat)) (h_precond : smallestMissing_precond l) :
    smallestMissing_postcond l (smallestMissing l h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
