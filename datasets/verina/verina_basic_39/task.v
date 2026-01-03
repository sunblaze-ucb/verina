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
Definition rotateRight_precond_dec (l : (list Z)) (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition rotateRight_precond (l : (list Z)) (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition rotateRight (l : (list Z)) (n : nat) (h_precond : rotateRight_precond l n) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition rotateRight_postcond_dec (l : (list Z)) (n : nat) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition rotateRight_postcond (l : (list Z)) (n : nat) (result : (list Z)) (h_precond : rotateRight_precond l n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem rotateRight_postcond_satisfied (l : (list Z)) (n : nat) (h_precond : rotateRight_precond l n) :
    rotateRight_postcond l n (rotateRight l n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
