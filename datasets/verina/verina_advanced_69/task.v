(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted_strict (xs : list Z) : bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <? y) && is_sorted_strict rest
  end.
(* !benchmark @end precond_aux *)

Definition searchInsert_precond (xs : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  is_sorted_strict xs
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint searchInsert_helper (ys : list Z) (target : Z) (idx : nat) : nat :=
  match ys with
  | [] => idx
  | y :: ys' =>
      if (target <=? y)
      then idx
      else searchInsert_helper ys' target (idx + 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition searchInsert (xs : (list Z)) (target : Z) : nat :=
  (* !benchmark @start code *)
  match xs with
  | [] => O
  | _ :: _ => searchInsert_helper xs target O
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: t, S n' => nth_Z t n' default
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.
(* !benchmark @end postcond_aux *)

Definition searchInsert_postcond (xs : (list Z)) (target : Z) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let allBeforeLess := forallb (fun i => (nth_Z xs i 0 <? target)) (range result) in
  let inBounds := (result <=? length xs)%nat in
  let insertedCorrectly := implb (result <? length xs)%nat (target <=? nth_Z xs result 0) in
  inBounds && allBeforeLess && insertedCorrectly
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem searchInsert_postcond_satisfied (xs : (list Z)) (target : Z) :
    searchInsert_precond xs target = true ->
    searchInsert_postcond xs target (searchInsert xs target) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
