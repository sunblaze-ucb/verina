(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted_Z (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl => (x <=? y) && is_sorted_Z tl
  end.

Definition mergeSortedLists_precond_dec (arr1 : list Z) (arr2 : list Z) : bool :=
  is_sorted_Z arr1 && is_sorted_Z arr2.
(* !benchmark @end precond_aux *)

Definition mergeSortedLists_precond (arr1 : (list Z)) (arr2 : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  Sorted Z.le arr1 /\ Sorted Z.le arr2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint merge (xs : list Z) (ys : list Z) : list Z :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xt, y :: yt =>
      if (x <=? y)%Z then
        x :: merge xt (y :: yt)
      else
        y :: merge (x :: xt) yt
  end.
(* !benchmark @end code_aux *)

Definition mergeSortedLists (arr1 : (list Z)) (arr2 : (list Z)) (h_precond : mergeSortedLists_precond arr1 arr2) : (list Z) :=
  (* !benchmark @start code *)
  merge arr1 arr2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_permutation_Z (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: xs =>
      if existsb (Z.eqb x) l2 then
        is_permutation_Z xs (remove Z.eq_dec x l2)
      else
        false
  end.

Definition mergeSortedLists_postcond_dec (arr1 : list Z) (arr2 : list Z) (result : list Z) : bool :=
  is_sorted_Z result && is_permutation_Z (arr1 ++ arr2) result.
(* !benchmark @end postcond_aux *)

Definition mergeSortedLists_postcond (arr1 : (list Z)) (arr2 : (list Z)) (result : (list Z)) (h_precond : mergeSortedLists_precond arr1 arr2) : Prop :=
  (* !benchmark @start postcond *)
  Sorted Z.le result /\ Permutation (arr1 ++ arr2) result
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
