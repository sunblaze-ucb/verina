(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Reals.
Open Scope R_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition has_close_elements_precond_dec (numbers : (list R)) (threshold : R) : bool := true.
(* !benchmark @end precond_aux *)

Definition has_close_elements_precond (numbers : (list R)) (threshold : R) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition has_close_elements (numbers : (list R)) (threshold : R) (h_precond : has_close_elements_precond numbers threshold) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition has_close_elements_postcond_dec (numbers : (list R)) (threshold : R) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition has_close_elements_postcond (numbers : (list R)) (threshold : R) (result : bool) (h_precond : has_close_elements_precond numbers threshold) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem has_close_elements_postcond_satisfied (numbers : (list R)) (threshold : R) (h_precond : has_close_elements_precond numbers threshold) :
    has_close_elements_postcond numbers threshold (has_close_elements numbers threshold h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
