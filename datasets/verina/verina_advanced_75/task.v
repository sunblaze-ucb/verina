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
(* Helper function to compute maximum of two integers *)
Definition max_z (a b : Z) : Z :=
  if (a >=? b)%Z then a else b.

(* Fold function for Kadane's algorithm *)
Definition kadane_step (acc : Z * Z) (x : Z) : Z * Z :=
  let (cur, maxSoFar) := acc in
  let newCur := max_z x (cur + x) in
  let newMax := max_z maxSoFar newCur in
  (newCur, newMax).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition task_code_precond_dec (sequence : list Z) : bool :=
  Nat.ltb 0%nat (length sequence).
(* !benchmark @end precond_aux *)

Definition task_code_precond (sequence : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length sequence > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers needed *)
(* !benchmark @end code_aux *)

Definition task_code (sequence : (list Z)) (h_precond : task_code_precond sequence) : Z :=
  (* !benchmark @start code *)
  match sequence with
| [] => 0
| x :: xs =>
    let (_, maxSoFar) := fold_left kadane_step xs (x, x) in
    maxSoFar
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Generate all contiguous subarrays *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => l
  | _, [] => []
  | S n', _ :: l' => drop n' l'
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: l' => x :: take n' l'
  end.

Definition flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  flat_map f l.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition subArrays (sequence : list Z) : list (list Z) :=
  flat_map (fun start =>
    map (fun len =>
      take len (drop start sequence))
      (range (S ((length sequence - start)%nat))))
    (range (S (length sequence))).

Definition subArraySums (sequence : list Z) : list Z :=
  map sum_list (filter (fun l => negb (match l with [] => true | _ => false end)) (subArrays sequence)).

(* Helper to check if list contains element *)
Fixpoint contains_z (l : list Z) (x : Z) : Prop :=
  match l with
  | [] => False
  | y :: ys => y = x \/ contains_z ys x
  end.

Fixpoint contains_z_dec (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | y :: ys => (y =? x)%Z || contains_z_dec ys x
  end.

(* Helper to check if all elements satisfy predicate *)
Fixpoint all_z (f : Z -> Prop) (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => f x /\ all_z f xs
  end.

Fixpoint all_z_dec (f : Z -> bool) (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => f x && all_z_dec f xs
  end.

Definition task_code_postcond_dec (sequence : list Z) (result : Z) : bool :=
  let sums := subArraySums sequence in
  contains_z_dec sums result && all_z_dec (fun x => (x <=? result)%Z) sums.
(* !benchmark @end postcond_aux *)

Definition task_code_postcond (sequence : (list Z)) (result : Z) (h_precond : task_code_precond sequence) : Prop :=
  (* !benchmark @start postcond *)
  let subArrays_list := subArrays sequence in
let subArraySums_list := subArraySums sequence in
contains_z subArraySums_list result /\ all_z (fun x => x <= result) subArraySums_list
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem task_code_postcond_satisfied (sequence : (list Z)) (h_precond : task_code_precond sequence) :
    task_code_postcond sequence (task_code sequence h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
