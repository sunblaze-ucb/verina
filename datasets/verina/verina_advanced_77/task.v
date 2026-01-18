(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to get element at index with default *)
Fixpoint nth_default {A : Type} (l : list A) (n : nat) (default : A) : A :=
  match n, l with
  | O, x :: _ => x
  | S n', _ :: tl => nth_default tl n' default
  | _, [] => default
  end.

(* Helper to generate range [0..n) *)
Fixpoint range_helper (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => acc
  | S n' => range_helper n' (n' :: acc)
  end.

Definition range (n : nat) : list nat :=
  range_helper n [].

(* Helper to take first n elements *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: xs => x :: take n' xs
  end.

(* Helper to drop first n elements *)
Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, l => l
  | _, [] => []
  | S n', _ :: xs => drop n' xs
  end.

(* Fold left for nat *)
Fixpoint fold_left_nat (f : nat -> nat -> nat) (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => fold_left_nat f xs (f acc x)
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition trapRainWater_precond_dec (height : list nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition trapRainWater_precond (height : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Imperative-style loop translation using fixpoint *)
Fixpoint trapRainWater_loop (height : list nat) (left right leftMax rightMax water : nat) (fuel : nat) : nat :=
  match fuel with
  | O => water
  | S fuel' =>
      if Nat.ltb left right then
        let hLeft := nth_default height left 0%nat in
        let hRight := nth_default height right 0%nat in
        if Nat.ltb hLeft hRight then
          let newLeftMax := if Nat.leb leftMax hLeft then hLeft else leftMax in
          let newWater := if Nat.leb leftMax hLeft then water else water + (leftMax - hLeft) in
          trapRainWater_loop height (left + 1) right newLeftMax rightMax newWater fuel'
        else
          let newRightMax := if Nat.leb rightMax hRight then hRight else rightMax in
          let newWater := if Nat.leb rightMax hRight then water else water + (rightMax - hRight) in
          trapRainWater_loop height left (right - 1) leftMax newRightMax newWater fuel'
      else
        water
  end.
(* !benchmark @end code_aux *)

Definition trapRainWater (height : (list nat)) (h_precond : trapRainWater_precond height) : nat :=
  (* !benchmark @start code *)
  match length height with
| O => 0%nat
| S _ =>
    let right := length height - 1 in
    trapRainWater_loop height 0%nat right 0%nat 0%nat 0%nat (length height)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition waterAt (height : list nat) : list nat :=
  map (fun i =>
    let lmax := fold_left_nat Nat.max (take (i + 1) height) 0%nat in
    let rmax := fold_left_nat Nat.max (drop i height) 0%nat in
    Nat.min lmax rmax - nth_default height i 0%nat)
    (range (length height)).

Definition trapRainWater_postcond_dec (height : list nat) (result : nat) : bool :=
  let expected := fold_left_nat Nat.add (waterAt height) 0%nat in
  Nat.eqb (result - expected) 0%nat && Nat.leb expected result.
(* !benchmark @end postcond_aux *)

Definition trapRainWater_postcond (height : (list nat)) (result : nat) (h_precond : trapRainWater_precond height) : Prop :=
  (* !benchmark @start postcond *)
  let expected := fold_left_nat Nat.add (waterAt height) 0%nat in
  result - expected = 0%nat /\ expected <= result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem trapRainWater_postcond_satisfied (height : (list nat)) (h_precond : trapRainWater_precond height) :
    trapRainWater_postcond height (trapRainWater height h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
