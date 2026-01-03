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
Definition lastPosition_precond_dec (arr : (list Z)) (elem : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition lastPosition_precond (arr : (list Z)) (elem : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition lastPosition (arr : (list Z)) (elem : Z) (h_precond : lastPosition_precond arr elem) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition lastPosition_postcond_dec (arr : (list Z)) (elem : Z) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition lastPosition_postcond (arr : (list Z)) (elem : Z) (result : Z) (h_precond : lastPosition_precond arr elem) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem lastPosition_postcond_satisfied (arr : (list Z)) (elem : Z) (h_precond : lastPosition_precond arr elem) :
    lastPosition_postcond arr elem (lastPosition arr elem h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
