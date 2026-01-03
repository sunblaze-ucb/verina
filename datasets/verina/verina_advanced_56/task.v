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
Definition moveZeroes_precond_dec (xs : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition moveZeroes_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition moveZeroes (xs : (list Z)) (h_precond : moveZeroes_precond xs) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition moveZeroes_postcond_dec (xs : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition moveZeroes_postcond (xs : (list Z)) (result : (list Z)) (h_precond : moveZeroes_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem moveZeroes_postcond_satisfied (xs : (list Z)) (h_precond : moveZeroes_precond xs) :
    moveZeroes_postcond xs (moveZeroes xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
