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
Definition copy_precond_dec (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition copy_precond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition copy (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (h_precond : copy_precond src sStart dest dStart len) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition copy_postcond_dec (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition copy_postcond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (result : (list Z)) (h_precond : copy_precond src sStart dest dStart len) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem copy_postcond_satisfied (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (h_precond : copy_precond src sStart dest dStart len) :
    copy_postcond src sStart dest dStart len (copy src sStart dest dStart len h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
