(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition partitionEvensOdds_precond (nums : (list nat)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint partitionEvensOdds_helper (nums : list nat) : (list nat * list nat) :=
  match nums with
  | [] => ([], [])
  | x :: xs =>
    let (evens, odds) := partitionEvensOdds_helper xs in
    if (x mod 2 =? 0)%nat then (x :: evens, odds)
    else (evens, x :: odds)
  end.
(* !benchmark @end code_aux *)

Definition partitionEvensOdds (nums : (list nat)) : (list nat * list nat) :=
  (* !benchmark @start code *)
  partitionEvensOdds_helper nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition partitionEvensOdds_postcond (nums : (list nat)) (result : (list nat * list nat)) : bool :=
  (* !benchmark @start postcond *)
  let evens := fst result in
  let odds := snd result in
  list_nat_eqb (evens ++ odds) (filter (fun n => (n mod 2 =? 0)%nat) nums ++ filter (fun n => (n mod 2 =? 1)%nat) nums) &&
  forallb (fun n => (n mod 2 =? 0)%nat) evens &&
  forallb (fun n => (n mod 2 =? 1)%nat) odds
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem partitionEvensOdds_postcond_satisfied (nums : (list nat)) :
    partitionEvensOdds_precond nums = true ->
    partitionEvensOdds_postcond nums (partitionEvensOdds nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
