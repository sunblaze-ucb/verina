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
Definition LinearSearch_precond_dec (a : (list Z)) (e : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition LinearSearch_precond (a : (list Z)) (e : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition LinearSearch (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LinearSearch_postcond_dec (a : (list Z)) (e : Z) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition LinearSearch_postcond (a : (list Z)) (e : Z) (result : nat) (h_precond : LinearSearch_precond a e) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem LinearSearch_postcond_satisfied (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) :
    LinearSearch_postcond a e (LinearSearch a e h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
