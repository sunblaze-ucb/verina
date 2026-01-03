(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition LinearSearch3_precond_dec (a : (list Z)) (P : (Z -> bool)) : bool := true.
(* !benchmark @end precond_aux *)

Definition LinearSearch3_precond (a : (list Z)) (P : (Z -> bool)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition LinearSearch3 (a : (list Z)) (P : (Z -> bool)) (h_precond : LinearSearch3_precond a P) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LinearSearch3_postcond_dec (a : (list Z)) (P : (Z -> bool)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition LinearSearch3_postcond (a : (list Z)) (P : (Z -> bool)) (result : nat) (h_precond : LinearSearch3_precond a P) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem LinearSearch3_postcond_satisfied (a : (list Z)) (P : (Z -> bool)) (h_precond : LinearSearch3_precond a P) :
    LinearSearch3_postcond a P (LinearSearch3 a P h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.