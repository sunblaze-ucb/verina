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

(* !benchmark @end precond_aux *)

Definition isPeakValley_precond (lst : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint aux (l : list Z) (increasing : bool) (startedDecreasing : bool) : bool :=
  match l with
  | [] => increasing && startedDecreasing
  | [_] => increasing && startedDecreasing
  | x :: ((y :: rest) as tail) =>
    if (x <? y)%Z then
      if startedDecreasing then false
      else aux tail true startedDecreasing
    else if (x >? y)%Z then
      if increasing then aux tail increasing true
      else false
    else false
  end.
(* !benchmark @end code_aux *)

Definition isPeakValley (lst : (list Z)) : bool :=
  (* !benchmark @start code *)
  aux lst false false
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default (d : Z) (l : list Z) (n : nat) : Z :=
  match l with
  | [] => d
  | h :: t => match n with
              | O => h
              | S n' => nth_default d t n'
              end
  end.

Definition get_elem (l : list Z) (i : nat) : Z := nth_default 0 l i.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint forallb_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | h :: t => f h && forallb_nat f t
  end.

Definition check_strictly_increasing (lst : list Z) (p : nat) : bool :=
  forallb_nat (fun i => (get_elem lst i <? get_elem lst (i + 1)%nat)%Z) (range p).

Definition check_strictly_decreasing (lst : list Z) (p : nat) (len : nat) : bool :=
  forallb_nat (fun i => (get_elem lst (p + i)%nat >? get_elem lst (p + i + 1)%nat)%Z) (range (len - 1 - p)%nat).

Definition is_valid_peak (lst : list Z) (len : nat) (p : nat) : bool :=
  (1 <=? p)%nat && (p <? len - 1)%nat && check_strictly_increasing lst p && check_strictly_decreasing lst p len.

Fixpoint filter_nat (f : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => if f h then h :: filter_nat f t else filter_nat f t
  end.

Definition valid_peaks (lst : list Z) : list nat :=
  let len := length lst in
  filter_nat (is_valid_peak lst len) (range len).
(* !benchmark @end postcond_aux *)

Definition isPeakValley_postcond (lst : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let validPeaks := valid_peaks lst in
  implb (negb (length validPeaks =? 0)%nat) result && implb ((length validPeaks =? 0)%nat) (negb result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPeakValley_postcond_satisfied (lst : (list Z)) :
    isPeakValley_precond lst = true ->
    isPeakValley_postcond lst (isPeakValley lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
