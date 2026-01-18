(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Fixpoint exists_index_satisfying (a : list Z) (P : Z -> bool) (i : nat) : bool :=
  match a with
  | [] => false
  | x :: xs =>
    if Nat.ltb i (length (x :: xs)) then
      if P x then true
      else exists_index_satisfying xs P (S i)
    else false
  end.

Definition LinearSearch3_precond_dec (a : list Z) (P : Z -> bool) : bool :=
  exists_index_satisfying a P 0%nat.
(* !benchmark @end precond_aux *)

Definition LinearSearch3_precond (a : (list Z)) (P : (Z -> bool)) : Prop :=
  (* !benchmark @start precond *)
  exists i, (i < length a)%nat /\ P (nth i a 0%Z) = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint LinearSearch3_loop (a : list Z) (P : Z -> bool) (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => 0%nat
  | S fuel' =>
    if Nat.ltb n (length a) then
      if P (nth n a 0%Z) then n
      else LinearSearch3_loop a P (n + 1)%nat fuel'
    else 0%nat
  end.
(* !benchmark @end code_aux *)

Definition LinearSearch3 (a : (list Z)) (P : (Z -> bool)) (h_precond : LinearSearch3_precond a P) : nat :=
  (* !benchmark @start code *)
  LinearSearch3_loop a P 0%nat (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Fixpoint all_before_fail (a : list Z) (P : Z -> bool) (result : nat) (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
    if Nat.ltb k' result then
      if P (nth k' a 0%Z) then false
      else all_before_fail a P result k'
    else all_before_fail a P result k'
  end.

Definition LinearSearch3_postcond_dec (a : list Z) (P : Z -> bool) (result : nat) : bool :=
  andb (andb (Nat.ltb result (length a)) (P (nth result a 0%Z)))
       (all_before_fail a P result result).
(* !benchmark @end postcond_aux *)

Definition LinearSearch3_postcond (a : (list Z)) (P : (Z -> bool)) (result : nat) (h_precond : LinearSearch3_precond a P) : Prop :=
  (* !benchmark @start postcond *)
  (result < length a)%nat /\ P (nth result a 0%Z) = true /\ (forall k, (k < result)%nat -> P (nth k a 0%Z) = false)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch3_postcond_satisfied (a : (list Z)) (P : (Z -> bool)) (h_precond : LinearSearch3_precond a P) :
    LinearSearch3_postcond a P (LinearSearch3 a P h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
