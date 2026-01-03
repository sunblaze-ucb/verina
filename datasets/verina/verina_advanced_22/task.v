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
Definition isPeakValley_precond_dec (lst : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition isPeakValley_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isPeakValley (lst : (list Z)) (h_precond : isPeakValley_precond lst) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isPeakValley_postcond_dec (lst : (list Z)) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition isPeakValley_postcond (lst : (list Z)) (result : bool) (h_precond : isPeakValley_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem isPeakValley_postcond_satisfied (lst : (list Z)) (h_precond : isPeakValley_precond lst) :
    isPeakValley_postcond lst (isPeakValley lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
