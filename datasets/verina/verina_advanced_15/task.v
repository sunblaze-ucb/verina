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
Definition increasingTriplet_precond_dec (nums : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition increasingTriplet_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition increasingTriplet (nums : (list Z)) (h_precond : increasingTriplet_precond nums) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition increasingTriplet_postcond_dec (nums : (list Z)) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition increasingTriplet_postcond (nums : (list Z)) (result : bool) (h_precond : increasingTriplet_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem increasingTriplet_postcond_satisfied (nums : (list Z)) (h_precond : increasingTriplet_precond nums) :
    increasingTriplet_postcond nums (increasingTriplet nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
