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
Definition searchInsert_precond_dec (xs : (list Z)) (target : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition searchInsert_precond (xs : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition searchInsert (xs : (list Z)) (target : Z) (h_precond : searchInsert_precond xs target) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition searchInsert_postcond_dec (xs : (list Z)) (target : Z) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition searchInsert_postcond (xs : (list Z)) (target : Z) (result : nat) (h_precond : searchInsert_precond xs target) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem searchInsert_postcond_satisfied (xs : (list Z)) (target : Z) (h_precond : searchInsert_precond xs target) :
    searchInsert_postcond xs target (searchInsert xs target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
