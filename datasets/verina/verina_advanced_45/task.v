(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxSubarraySum_precond_dec (xs : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition maxSubarraySum_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxSubarraySum_helper (lst : list Z) (curMax : Z) (globalMax : Z) : Z :=
  match lst with
  | [] => globalMax
  | x :: rest =>
      let newCurMax := Z.max x (curMax + x) in
      let newGlobal := Z.max globalMax newCurMax in
      maxSubarraySum_helper rest newCurMax newGlobal
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySum (xs : (list Z)) (h_precond : maxSubarraySum_precond xs) : Z :=
  (* !benchmark @start code *)
  match xs with
| [] => 0
| x :: rest => maxSubarraySum_helper rest x x
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Lia.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => l
  | S n', [] => []
  | S n', _ :: tl => drop n' tl
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | S n', [] => []
  | S n', hd :: tl => hd :: take n' tl
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint range' (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: range' (S start) len'
  end.

Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (x + sum_list xs)%Z
  end.

Fixpoint list_any {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => orb (f x) (list_any f xs)
  end.

Fixpoint list_all {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (f x) (list_all f xs)
  end.

Definition subarray_sums (xs : list Z) : list Z :=
  flat_map (fun start =>
    map (fun len =>
      sum_list (take len (drop start xs))
    ) (range' 1%nat ((length xs) - start)%nat)
  ) (range ((length xs) + 1%nat)%nat).

Definition maxSubarraySum_postcond_dec (xs : list Z) (result : Z) : bool :=
  let subarray_sums_list := subarray_sums xs in
  let has_result_subarray := list_any (fun sum => (sum =? result)%Z) subarray_sums_list in
  let is_maximum := list_all (fun sum => (sum <=? result)%Z) subarray_sums_list in
  match xs with
  | [] => (result =? 0)%Z
  | _ => andb has_result_subarray is_maximum
  end.
(* !benchmark @end postcond_aux *)

Definition maxSubarraySum_postcond (xs : (list Z)) (result : Z) (h_precond : maxSubarraySum_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  let subarray_sums_list := subarray_sums xs in
let has_result_subarray := existsb (fun sum => (sum =? result)%Z) subarray_sums_list in
let is_maximum := forallb (fun sum => (sum <=? result)%Z) subarray_sums_list in
match xs with
| [] => result = 0
| _ => has_result_subarray = true /\ is_maximum = true
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySum_postcond_satisfied (xs : (list Z)) (h_precond : maxSubarraySum_precond xs) :
    maxSubarraySum_postcond xs (maxSubarraySum xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
