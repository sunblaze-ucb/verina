(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition maxCoverageAfterRemovingOne_precond_dec (intervals : (list (nat * nat))) : bool := true.
(* !benchmark @end precond_aux *)

Definition maxCoverageAfterRemovingOne_precond (intervals : (list (nat * nat))) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition maxCoverageAfterRemovingOne (intervals : (list (nat * nat))) (h_precond : maxCoverageAfterRemovingOne_precond intervals) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition maxCoverageAfterRemovingOne_postcond_dec (intervals : (list (nat * nat))) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition maxCoverageAfterRemovingOne_postcond (intervals : (list (nat * nat))) (result : nat) (h_precond : maxCoverageAfterRemovingOne_precond intervals) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem maxCoverageAfterRemovingOne_postcond_satisfied (intervals : (list (nat * nat))) (h_precond : maxCoverageAfterRemovingOne_precond intervals) :
    maxCoverageAfterRemovingOne_postcond intervals (maxCoverageAfterRemovingOne intervals h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.