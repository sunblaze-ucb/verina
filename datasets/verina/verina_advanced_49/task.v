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
Definition mergeSortedLists_precond_dec (arr1 : (list Z)) (arr2 : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition mergeSortedLists_precond (arr1 : (list Z)) (arr2 : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition mergeSortedLists (arr1 : (list Z)) (arr2 : (list Z)) (h_precond : mergeSortedLists_precond arr1 arr2) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition mergeSortedLists_postcond_dec (arr1 : (list Z)) (arr2 : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition mergeSortedLists_postcond (arr1 : (list Z)) (arr2 : (list Z)) (result : (list Z)) (h_precond : mergeSortedLists_precond arr1 arr2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem mergeSortedLists_postcond_satisfied (arr1 : (list Z)) (arr2 : (list Z)) (h_precond : mergeSortedLists_precond arr1 arr2) :
    mergeSortedLists_postcond arr1 arr2 (mergeSortedLists arr1 arr2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
