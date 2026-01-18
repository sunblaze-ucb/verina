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
(* No additional solution-level helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint StrictlySorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      match xs with
      | [] => True
      | y :: _ => x < y /\ StrictlySorted xs
      end
  end.

Fixpoint StrictlySorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: _ => (x <? y) && StrictlySorted_dec xs
      end
  end.

Definition searchInsert_precond_dec (xs : list Z) (target : Z) : bool :=
  StrictlySorted_dec xs.
(* !benchmark @end precond_aux *)

Definition searchInsert_precond (xs : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  StrictlySorted xs
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint searchInsert_helper (ys : list Z) (idx : nat) (target : Z) : nat :=
  match ys with
  | [] => idx
  | y :: ys' =>
      let isCurrent := y in
      let currentIndex := idx in
      let targetValue := target in
      let condition := (targetValue <=? isCurrent)%Z in
      if condition then
        currentIndex
      else
        let incrementedIndex := (currentIndex + 1)%nat in
        let rest := ys' in
        searchInsert_helper rest incrementedIndex target
  end.
(* !benchmark @end code_aux *)

Definition searchInsert (xs : (list Z)) (target : Z) (h_precond : searchInsert_precond xs target) : nat :=
  (* !benchmark @start code *)
  match xs with
| [] => 0%nat
| _ :: _ =>
    let startingIndex := 0%nat in
    let result := searchInsert_helper xs startingIndex target in
    result
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match n, l with
  | O, x :: _ => x
  | S m, _ :: t => nth_Z t m default
  | _, [] => default
  end.

Fixpoint all_indices_less (xs : list Z) (target : Z) (n : nat) : Prop :=
  match n with
  | O => True
  | S m => all_indices_less xs target m /\ (nth_Z xs m 0) < target
  end.

Fixpoint all_indices_less_dec (xs : list Z) (target : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S m => all_indices_less_dec xs target m && ((nth_Z xs m 0) <? target)
  end.

Definition searchInsert_postcond_dec (xs : list Z) (target : Z) (result : nat) : bool :=
  let allBeforeLess := all_indices_less_dec xs target result in
  let inBounds := (result <=? length xs)%nat in
  let insertedCorrectly :=
    if (result <? length xs)%nat then (target <=? nth_Z xs result 0)%Z else true
  in
  inBounds && allBeforeLess && insertedCorrectly.
(* !benchmark @end postcond_aux *)

Definition searchInsert_postcond (xs : (list Z)) (target : Z) (result : nat) (h_precond : searchInsert_precond xs target) : Prop :=
  (* !benchmark @start postcond *)
  let allBeforeLess := all_indices_less xs target result in
let inBounds := (result <= length xs)%nat in
let insertedCorrectly := (result < length xs)%nat -> target <= nth_Z xs result 0 in
inBounds /\ allBeforeLess /\ insertedCorrectly
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem searchInsert_postcond_satisfied (xs : (list Z)) (target : Z) (h_precond : searchInsert_precond xs target) :
    searchInsert_postcond xs target (searchInsert xs target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
