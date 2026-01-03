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
Definition Find_precond_dec (a : (list Z)) (key : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition Find_precond (a : (list Z)) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition Find (a : (list Z)) (key : Z) (h_precond : Find_precond a key) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Find_postcond_dec (a : (list Z)) (key : Z) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition Find_postcond (a : (list Z)) (key : Z) (result : Z) (h_precond : Find_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem Find_postcond_satisfied (a : (list Z)) (key : Z) (h_precond : Find_precond a key) :
    Find_postcond a key (Find a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
