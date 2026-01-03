(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition smallestMissingNumber_precond_dec (s : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition smallestMissingNumber_precond (s : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition smallestMissingNumber (s : (list nat)) (h_precond : smallestMissingNumber_precond s) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition smallestMissingNumber_postcond_dec (s : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition smallestMissingNumber_postcond (s : (list nat)) (result : nat) (h_precond : smallestMissingNumber_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem smallestMissingNumber_postcond_satisfied (s : (list nat)) (h_precond : smallestMissingNumber_precond s) :
    smallestMissingNumber_postcond s (smallestMissingNumber s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
