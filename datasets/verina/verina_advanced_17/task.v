(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to insert an integer into a sorted list *)
Fixpoint insertElement (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: ys =>
      if (x <=? y)%Z then
        x :: y :: ys
      else
        y :: insertElement x ys
  end.

(* Helper function to sort a list using insertion sort *)
Fixpoint sortList (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition insertionSort_precond_dec (l : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition insertionSort_precond (l : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to check if a list is sorted *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      match xs with
      | [] => True
      | y :: rest => (x <= y)%Z /\ is_sorted xs
      end
  end.

(* Helper to check if two lists are permutations *)
Fixpoint count_occ (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if (x =? y)%Z then S (count_occ x ys) else count_occ x ys
  end.

Definition is_perm (l1 l2 : list Z) : Prop :=
  forall x : Z, count_occ x l1 = count_occ x l2.
(* !benchmark @end code_aux *)

Definition insertionSort (l : (list Z)) (h_precond : insertionSort_precond l) : (list Z) :=
  (* !benchmark @start code *)
  let result := sortList l in result
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Pairwise ordering predicate *)
Inductive Pairwise {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
  | Pairwise_nil : Pairwise R []
  | Pairwise_cons : forall x l, (forall y, In y l -> R x y) -> Pairwise R l -> Pairwise R (x :: l).

Definition insertionSort_postcond_dec (l : list Z) (result : list Z) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition insertionSort_postcond (l : (list Z)) (result : (list Z)) (h_precond : insertionSort_precond l) : Prop :=
  (* !benchmark @start postcond *)
  Pairwise (fun x y => (x <= y)%Z) result /\ is_perm l result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insertionSort_postcond_satisfied (l : (list Z)) (h_precond : insertionSort_precond l) :
    insertionSort_postcond l (insertionSort l h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
