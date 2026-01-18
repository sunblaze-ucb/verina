(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to update element at index in list *)
Fixpoint list_set (l : list Z) (idx : nat) (val : Z) : list Z :=
  match l, idx with
  | [], _ => []
  | x :: xs, 0%nat => val :: xs
  | x :: xs, S n => x :: list_set xs n val
  end.

(* Helper function to get element at index in list *)
Fixpoint list_get (l : list Z) (idx : nat) (default : Z) : Z :=
  match l, idx with
  | [], _ => default
  | x :: xs, 0%nat => x
  | x :: xs, S n => list_get xs n default
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition UpdateElements_precond_dec (a : list Z) : bool :=
  (8 <=? length a)%nat.
(* !benchmark @end precond_aux *)

Definition UpdateElements_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a >= 8)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code auxiliaries needed *)
(* !benchmark @end code_aux *)

Definition UpdateElements (a : (list Z)) (h_precond : UpdateElements_precond a) : (list Z) :=
  (* !benchmark @start code *)
  let a1 := list_set a 4%nat ((list_get a 4%nat 0%Z) + 3)%Z in
  let a2 := list_set a1 7%nat 516%Z in
  a2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition UpdateElements_postcond_dec (a : list Z) (result : list Z) : bool :=
  (list_get result 4%nat 0%Z =? (list_get a 4%nat 0%Z) + 3)%Z &&
  (list_get result 7%nat 0%Z =? 516)%Z &&
  (forallb (fun i => 
    if (i <? length a)%nat then
      if Nat.eqb i 4%nat then true
      else if Nat.eqb i 7%nat then true
      else (list_get result i 0%Z =? list_get a i 0%Z)%Z
    else true
  ) (seq 0%nat (length a))).
(* !benchmark @end postcond_aux *)

Definition UpdateElements_postcond (a : (list Z)) (result : (list Z)) (h_precond : UpdateElements_precond a) : Prop :=
  (* !benchmark @start postcond *)
  list_get result 4%nat 0%Z = ((list_get a 4%nat 0%Z) + 3)%Z /\
  list_get result 7%nat 0%Z = 516%Z /\
  (forall i, (i < length a)%nat -> i <> 4%nat -> i <> 7%nat -> list_get result i 0%Z = list_get a i 0%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem UpdateElements_postcond_satisfied (a : (list Z)) (h_precond : UpdateElements_precond a) :
    UpdateElements_postcond a (UpdateElements a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
