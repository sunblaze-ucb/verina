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
Definition onlineMax_precond_dec (a : (list Z)) (x : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition onlineMax_precond (a : (list Z)) (x : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition onlineMax (a : (list Z)) (x : nat) (h_precond : onlineMax_precond a x) : (Z  * nat) :=
  (* !benchmark @start code *)
  (0%Z, 0%nat)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition onlineMax_postcond_dec (a : (list Z)) (x : nat) (result : (Z  * nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition onlineMax_postcond (a : (list Z)) (x : nat) (result : (Z  * nat)) (h_precond : onlineMax_precond a x) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem onlineMax_postcond_satisfied (a : (list Z)) (x : nat) (h_precond : onlineMax_precond a x) :
    onlineMax_postcond a x (onlineMax a x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.