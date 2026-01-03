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
Definition SelectionSort_precond_dec (a : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition SelectionSort_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition SelectionSort (a : (list Z)) (h_precond : SelectionSort_precond a) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SelectionSort_postcond_dec (a : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition SelectionSort_postcond (a : (list Z)) (result : (list Z)) (h_precond : SelectionSort_precond a) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem SelectionSort_postcond_satisfied (a : (list Z)) (h_precond : SelectionSort_precond a) :
    SelectionSort_postcond a (SelectionSort a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
