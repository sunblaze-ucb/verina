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
Require Import Coq.Arith.Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to generate range [0, n) *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

(* Get element at index with default *)
Fixpoint nth_default {A : Type} (default : A) (l : list A) (n : nat) : A :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_default default xs n'
  end.

(* Set element at index *)
Fixpoint set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: xs, O => v :: xs
  | x :: xs, S n' => x :: set_nth xs n' v
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SelectionSort_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition SelectionSort_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Find minimum index in range [start, finish) *)
Fixpoint findMinIndexInRange (arr : list Z) (start finish : nat) : nat :=
  let indices := range (finish - start) in
  fold_left (fun minIdx i =>
    let currIdx := (start + i)%nat in
    if (nth_default 0%Z arr currIdx <? nth_default 0%Z arr minIdx)%Z 
    then currIdx 
    else minIdx
  ) indices start.

(* Swap elements at positions i and j *)
Definition swap (a : list Z) (i j : nat) : list Z :=
  if (Nat.ltb i (length a) && Nat.ltb j (length a) && negb (Nat.eqb i j))%bool then
    let temp := nth_default 0%Z a i in
    let a' := set_nth a i (nth_default 0%Z a j) in
    set_nth a' j temp
  else a.
(* !benchmark @end code_aux *)

Definition SelectionSort (a : (list Z)) (h_precond : SelectionSort_precond a) : (list Z) :=
  (* !benchmark @start code *)
  let indices := range (length a) in
  fold_left (fun arr i =>
    let minIdx := findMinIndexInRange arr i (length a) in
    swap arr i minIdx
  ) indices a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Check if list is sorted in non-decreasing order *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => 
      match xs with
      | [] => True
      | y :: _ => (x <= y)%Z /\ is_sorted xs
      end
  end.

(* Check if two lists are permutations (same elements with same multiplicities) *)
Definition is_perm (l1 l2 : list Z) : Prop :=
  forall x, count_occ Z.eq_dec l1 x = count_occ Z.eq_dec l2 x.

(* Decidable version of sorted check *)
Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: _ => (x <=? y)%Z && is_sorted_dec xs
      end
  end.

(* Decidable version of permutation check (limited) *)
Fixpoint is_perm_dec (l1 l2 : list Z) : bool :=
  (Nat.eqb (length l1) (length l2)) && 
  (forallb (fun x => Nat.eqb (count_occ Z.eq_dec l1 x) (count_occ Z.eq_dec l2 x)) l1).

Definition SelectionSort_postcond_dec (a result : list Z) : bool :=
  is_sorted_dec result && is_perm_dec a result.
(* !benchmark @end postcond_aux *)

Definition SelectionSort_postcond (a : (list Z)) (result : (list Z)) (h_precond : SelectionSort_precond a) : Prop :=
  (* !benchmark @start postcond *)
  is_sorted result /\ is_perm a result
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
