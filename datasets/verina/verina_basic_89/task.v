(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition SetToSeq_precond_dec (s : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition SetToSeq_precond (s : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition SetToSeq (s : (list Z)) (h_precond : SetToSeq_precond s) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SetToSeq_postcond_dec (s : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition SetToSeq_postcond (s : (list Z)) (result : (list Z)) (h_precond : SetToSeq_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem SetToSeq_postcond_satisfied (s : (list Z)) (h_precond : SetToSeq_precond s) :
    SetToSeq_postcond s (SetToSeq s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
