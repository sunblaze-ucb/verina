(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition addTwoNumbers_precond_dec (l1 : (list nat)) (l2 : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition addTwoNumbers_precond (l1 : (list nat)) (l2 : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition addTwoNumbers (l1 : (list nat)) (l2 : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) : (list nat) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition addTwoNumbers_postcond_dec (l1 : (list nat)) (l2 : (list nat)) (result : (list nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition addTwoNumbers_postcond (l1 : (list nat)) (l2 : (list nat)) (result : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem addTwoNumbers_postcond_satisfied (l1 : (list nat)) (l2 : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) :
    addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
