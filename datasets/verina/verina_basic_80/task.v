(* !benchmark @start import type=task *)
Require Import Bool.
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
Definition only_once_precond_dec (a : (list Z)) (key : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition only_once_precond (a : (list Z)) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition only_once (a : (list Z)) (key : Z) (h_precond : only_once_precond a key) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition only_once_postcond_dec (a : (list Z)) (key : Z) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition only_once_postcond (a : (list Z)) (key : Z) (result : bool) (h_precond : only_once_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem only_once_postcond_satisfied (a : (list Z)) (key : Z) (h_precond : only_once_precond a key) :
    only_once_postcond a key (only_once a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
