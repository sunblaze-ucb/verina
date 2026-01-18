(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
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
Definition isPeakValley_precond_dec (lst : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isPeakValley_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPeakValley_aux (l : list Z) (prev : option Z) (increasing : bool) (startedDecreasing : bool) : bool :=
  match l with
  | [] => 
      match prev with
      | None => false
      | Some _ => andb increasing startedDecreasing
      end
  | x :: rest =>
      match prev with
      | None => isPeakValley_aux rest (Some x) increasing startedDecreasing
      | Some p =>
          if (p <? x)%Z then
            if startedDecreasing then false
            else isPeakValley_aux rest (Some x) true startedDecreasing
          else if (p >? x)%Z then
            if increasing then isPeakValley_aux rest (Some x) increasing true
            else false
          else false
      end
  end.
(* !benchmark @end code_aux *)

Definition isPeakValley (lst : (list Z)) (h_precond : isPeakValley_precond lst) : bool :=
  (* !benchmark @start code *)
  isPeakValley_aux lst None false false
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Arith.

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => []
  | S m => range m ++ [m]
  end.

Fixpoint nth_default_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, 0%nat => x
  | _ :: xs, S m => nth_default_Z xs m default
  end.

Fixpoint all_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (f x) (all_nat f xs)
  end.

Fixpoint filter_nat (f : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter_nat f xs else filter_nat f xs
  end.

Definition check_peak (lst : list Z) (len : nat) (p : nat) : bool :=
  andb (andb (1 <=? p)%nat (p <? len - 1)%nat)
    (andb
      (all_nat (fun i => (nth_default_Z lst i 0 <? nth_default_Z lst (i + 1) 0)%Z) (range p))
      (all_nat (fun i => (nth_default_Z lst (p + i) 0 >? nth_default_Z lst (p + i + 1) 0)%Z) (range (len - 1 - p)))).

Definition isPeakValley_postcond_dec (lst : list Z) (result : bool) : bool :=
  let len := length lst in
  let validPeaks := filter_nat (check_peak lst len) (range len) in
  andb
    (implb (negb (Nat.eqb (length validPeaks) 0%nat)) result)
    (implb (Nat.eqb (length validPeaks) 0%nat) (negb result)).
(* !benchmark @end postcond_aux *)

Definition isPeakValley_postcond (lst : (list Z)) (result : bool) (h_precond : isPeakValley_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  let len := length lst in
  let validPeaks :=
    filter_nat (fun p => check_peak lst len p) (range len)
  in
  ((validPeaks <> []) -> result = true) /\
  ((length validPeaks = 0%nat) -> result = false)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPeakValley_postcond_satisfied (lst : (list Z)) (h_precond : isPeakValley_precond lst) :
    isPeakValley_postcond lst (isPeakValley lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
