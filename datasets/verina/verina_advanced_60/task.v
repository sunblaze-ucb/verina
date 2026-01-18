(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition partitionEvensOdds_precond_dec (nums : list nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition partitionEvensOdds_precond (nums : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint partitionEvensOdds_helper (nums : list nat) : (list nat * list nat) :=
  match nums with
  | [] => ([], [])
  | x :: xs =>
    let '(evens, odds) := partitionEvensOdds_helper xs in
    if Nat.eqb (x mod 2) 0%nat then (x :: evens, odds)
    else (evens, x :: odds)
  end.
(* !benchmark @end code_aux *)

Definition partitionEvensOdds (nums : (list nat)) (h_precond : partitionEvensOdds_precond nums) : (list nat * list nat) :=
  (* !benchmark @start code *)
  partitionEvensOdds_helper nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_nat (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (p x) (all_nat p xs)
  end.

Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => andb (Nat.eqb x y) (list_nat_eqb xs ys)
  | _, _ => false
  end.

Definition partitionEvensOdds_postcond_dec (nums : list nat) (result : list nat * list nat) : bool :=
  let evens := fst result in
  let odds := snd result in
  let filtered_evens := filter (fun n => Nat.eqb (n mod 2) 0%nat) nums in
  let filtered_odds := filter (fun n => Nat.eqb (n mod 2) 1%nat) nums in
  andb (andb (list_nat_eqb (evens ++ odds) (filtered_evens ++ filtered_odds))
             (all_nat (fun n => Nat.eqb (n mod 2) 0%nat) evens))
       (all_nat (fun n => Nat.eqb (n mod 2) 1%nat) odds).
(* !benchmark @end postcond_aux *)

Definition partitionEvensOdds_postcond (nums : (list nat)) (result : (list nat * list nat)) (h_precond : partitionEvensOdds_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let evens := fst result in
let odds := snd result in
evens ++ odds = filter (fun n => Nat.eqb (n mod 2) 0%nat) nums ++ filter (fun n => Nat.eqb (n mod 2) 1%nat) nums /\
Forall (fun n => Nat.eqb (n mod 2) 0%nat = true) evens /\
Forall (fun n => Nat.eqb (n mod 2) 1%nat = true) odds
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem partitionEvensOdds_postcond_satisfied (nums : (list nat)) (h_precond : partitionEvensOdds_precond nums) :
    partitionEvensOdds_postcond nums (partitionEvensOdds nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
