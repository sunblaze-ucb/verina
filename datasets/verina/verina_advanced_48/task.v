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
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition mergeSort_precond_dec (lst : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition mergeSort_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | y :: ys =>
      if (x <=? y)%Z then
        x :: sorted
      else
        y :: insert x ys
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let sortedRest := sort xs in
      insert x sortedRest
  end.
(* !benchmark @end code_aux *)

Definition mergeSort (lst : (list Z)) (h_precond : mergeSort_precond lst) : (list Z) :=
  (* !benchmark @start code *)
  sort lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Definition is_sorted (l : list Z) : Prop :=
  Sorted Z.le l.

Definition is_perm (l1 l2 : list Z) : Prop :=
  Permutation l1 l2.

Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl =>
      if (x <=? y)%Z then is_sorted_dec tl else false
  end.

Fixpoint is_perm_dec (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | _ :: _, [] => false
  | [], _ :: _ => false
  | _, _ => 
      (length l1 =? length l2)%nat
  end.

Definition mergeSort_postcond_dec (lst result : list Z) : bool :=
  andb (is_sorted_dec result) (is_perm_dec lst result).
(* !benchmark @end postcond_aux *)

Definition mergeSort_postcond (lst : (list Z)) (result : (list Z)) (h_precond : mergeSort_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  is_sorted result /\ is_perm lst result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSort_postcond_satisfied (lst : (list Z)) (h_precond : mergeSort_precond lst) :
    mergeSort_postcond lst (mergeSort lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
