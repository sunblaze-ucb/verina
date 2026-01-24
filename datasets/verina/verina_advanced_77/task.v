(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint nth_nat (l : list nat) (n : nat) (default : nat) : nat :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_nat t n' default
              end
  end.

Fixpoint foldl_max (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | h :: t => foldl_max t (max acc h)
  end.

Fixpoint take (n : nat) (l : list nat) : list nat :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | h :: t => h :: take n' t
            end
  end.

Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | _ :: t => drop n' t
            end
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition trapRainWater_precond (height : (list nat)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint trapRainWater_loop (height : list nat) (left right leftMax rightMax water : nat) (fuel : nat) : nat :=
  match fuel with
  | O => water
  | S fuel' =>
    if left <? right then
      let hLeft := nth_nat height left 0 in
      let hRight := nth_nat height right 0 in
      if hLeft <? hRight then
        if leftMax <=? hLeft then
          trapRainWater_loop height (S left) right hLeft rightMax water fuel'
        else
          trapRainWater_loop height (S left) right leftMax rightMax (water + (leftMax - hLeft)) fuel'
      else
        if rightMax <=? hRight then
          trapRainWater_loop height left (right - 1) leftMax hRight water fuel'
        else
          trapRainWater_loop height left (right - 1) leftMax rightMax (water + (rightMax - hRight)) fuel'
    else
      water
  end.
(* !benchmark @end code_aux *)

Definition trapRainWater (height : (list nat)) : nat :=
  (* !benchmark @start code *)
  let n := length height in
  match n with
  | O => 0
  | S _ => trapRainWater_loop height 0 (n - 1) 0 0 0 n
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition waterAt_fun (height : list nat) (i : nat) : nat :=
  let lmax := foldl_max (take (S i) height) 0 in
  let rmax := foldl_max (drop i height) 0 in
  min lmax rmax - nth_nat height i 0.

Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => (h + sum_list t)%nat
  end.

Definition waterAt_total (height : list nat) : nat :=
  sum_list (map (waterAt_fun height) (range (length height))).
(* !benchmark @end postcond_aux *)

Definition trapRainWater_postcond (height : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let expected := waterAt_total height in
  ((result - expected =? 0)%nat && (expected <=? result)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem trapRainWater_postcond_satisfied (height : (list nat)) :
    trapRainWater_precond height = true ->
    trapRainWater_postcond height (trapRainWater height) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
