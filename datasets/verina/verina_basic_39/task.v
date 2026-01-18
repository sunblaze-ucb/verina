(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Lia.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition rotateRight_precond_dec (l : list Z) (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition rotateRight_precond (l : (list Z)) (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nat_range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => nat_range n' ++ [n']
  end.

Definition rotateRight_helper (l : list Z) (len : nat) (n : nat) (i : nat) : Z :=
  let i_z := Z.of_nat i in
  let n_z := Z.of_nat n in
  let len_z := Z.of_nat len in
  let idx_int := ((i_z - n_z + len_z) mod len_z)%Z in
  let idx_nat := Z.to_nat idx_int in
  nth idx_nat l 0%Z.
(* !benchmark @end code_aux *)

Definition rotateRight (l : (list Z)) (n : nat) (h_precond : rotateRight_precond l n) : (list Z) :=
  (* !benchmark @start code *)
  let len := length l in
  if Nat.eqb len 0%nat then l
  else
    map (fun i => rotateRight_helper l len n i) (nat_range len)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition rotateRight_postcond_dec (l : list Z) (n : nat) (result : list Z) : bool :=
  Nat.eqb (length result) (length l).
(* !benchmark @end postcond_aux *)

Definition rotateRight_postcond (l : (list Z)) (n : nat) (result : (list Z)) (h_precond : rotateRight_precond l n) : Prop :=
  (* !benchmark @start postcond *)
  length result = length l /\
  (forall i : nat, (i < length l)%nat ->
    let len := length l in
    let i_z := Z.of_nat i in
    let n_z := Z.of_nat n in
    let len_z := Z.of_nat len in
    let rotated_index := Z.to_nat ((i_z - n_z + len_z) mod len_z)%Z in
    nth_error result i = nth_error l rotated_index)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rotateRight_postcond_satisfied (l : (list Z)) (n : nat) (h_precond : rotateRight_precond l n) :
    rotateRight_postcond l n (rotateRight l n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
