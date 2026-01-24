(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Recdef.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y) && is_sorted xs
    end
  end.
(* !benchmark @end precond_aux *)

Definition mergeSortedLists_precond (arr1 : (list Z)) (arr2 : (list Z)) : bool :=
  (* !benchmark @start precond *)
  is_sorted arr1 && is_sorted arr2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint merge_aux (fuel : nat) (xs ys : list Z) : list Z :=
  match fuel with
  | O => xs ++ ys  (* fallback if fuel runs out *)
  | S fuel' =>
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xt, y :: yt =>
      if x <=? y then
        x :: merge_aux fuel' xt ys
      else
        y :: merge_aux fuel' xs yt
    end
  end.

Definition merge (xs ys : list Z) : list Z :=
  merge_aux (length xs + length ys) xs ys.
(* !benchmark @end code_aux *)

Definition mergeSortedLists (arr1 : (list Z)) (arr2 : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  merge arr1 arr2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_sorted_post (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y) && is_sorted_post xs
    end
  end.

Fixpoint count_occ_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if h =? x then S (count_occ_Z x t) else count_occ_Z x t
  end.

Fixpoint is_perm (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | h :: t => (count_occ_Z h l1 =? count_occ_Z h l2)%nat && is_perm t l2
  end.
(* !benchmark @end postcond_aux *)

Definition mergeSortedLists_postcond (arr1 : (list Z)) (arr2 : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  is_sorted_post result && is_perm (arr1 ++ arr2) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSortedLists_postcond_satisfied (arr1 : (list Z)) (arr2 : (list Z)) :
    mergeSortedLists_precond arr1 arr2 = true ->
    mergeSortedLists_postcond arr1 arr2 (mergeSortedLists arr1 arr2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
