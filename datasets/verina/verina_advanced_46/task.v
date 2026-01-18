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
(* No solution-level auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxSubarraySum_precond_dec (numbers : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition maxSubarraySum_precond (numbers : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isAllNegative (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => if (x >=? 0)%Z then false else isAllNegative xs
  end.

Fixpoint findMaxProduct (l : list Z) (currMax : Z) (currSum : Z) : Z :=
  match l with
  | [] => currMax
  | x :: rest =>
      match rest with
      | [] => Z.max currMax x
      | y :: rest' =>
          let newSum := Z.max y (currSum + y) in
          let newMax := Z.max currMax newSum in
          findMaxProduct rest newMax newSum
      end
  end.

Definition handleList (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | xs =>
      if isAllNegative xs then
        0%nat
      else
        match xs with
        | [] => 0%nat
        | x :: rest =>
            let initialMax := Z.max 0 x in
            let startSum := Z.max 0 x in
            let result := findMaxProduct (x :: rest) initialMax startSum in
            Z.to_nat result
        end
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySum (numbers : (list Z)) (h_precond : maxSubarraySum_precond numbers) : Z :=
  (* !benchmark @start code *)
  Z.of_nat (handleList numbers)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => [0%nat]
  | S n' => 
      let rec := range n' in
      rec ++ [n]
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0%nat, _ => l
  | S n', [] => []
  | S n', _ :: tl => drop n' tl
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0%nat, _ => []
  | S n', [] => []
  | S n', hd :: tl => hd :: take n' tl
  end.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (x + sum xs)%Z
  end.

Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

Definition subArraySums (numbers : list Z) : list Z :=
  flat_map (fun start =>
    map (fun len =>
      sum (take len (drop start numbers)))
    (range (length numbers - start + 1)%nat))
  (range (length numbers + 1)%nat).

Fixpoint contains {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eq_dec x y then true else contains eq_dec x ys
  end.

Fixpoint all {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (p x) (all p xs)
  end.

Definition maxSubarraySum_postcond_dec (numbers : list Z) (result : Z) : bool :=
  let sums := subArraySums numbers in
  andb (contains Z.eq_dec result sums) (all (fun x => (x <=? result)%Z) sums).
(* !benchmark @end postcond_aux *)

Definition maxSubarraySum_postcond (numbers : (list Z)) (result : Z) (h_precond : maxSubarraySum_precond numbers) : Prop :=
  (* !benchmark @start postcond *)
  let subArraySums :=
  flat_map (fun start =>
    map (fun len =>
      sum (take len (drop start numbers)))
    (range (length numbers - start + 1)%nat))
  (range (length numbers + 1)%nat) in
In result subArraySums /\ Forall (fun x => (x <= result)%Z) subArraySums
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySum_postcond_satisfied (numbers : (list Z)) (h_precond : maxSubarraySum_precond numbers) :
    maxSubarraySum_postcond numbers (maxSubarraySum numbers h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
