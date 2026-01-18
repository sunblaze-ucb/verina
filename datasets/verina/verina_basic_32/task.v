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
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to update element at index in a list *)
Fixpoint list_set (l : list Z) (n : nat) (v : Z) : list Z :=
  match l, n with
  | [], _ => []
  | _ :: tl, O => v :: tl
  | hd :: tl, S n' => hd :: list_set tl n' v
  end.

(* Helper to get element at index with default for out of bounds *)
Fixpoint list_get (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | hd :: _, O => hd
  | _ :: tl, S n' => list_get tl n' default
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition swapFirstAndLast_precond_dec (a : list Z) : bool :=
  (0 <? length a)%nat.
(* !benchmark @end precond_aux *)

Definition swapFirstAndLast_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers *)
(* !benchmark @end code_aux *)

Definition swapFirstAndLast (a : (list Z)) (h_precond : swapFirstAndLast_precond a) : (list Z) :=
  (* !benchmark @start code *)
  let first := list_get a 0%nat 0 in
  let last := list_get a (length a - 1)%nat 0 in
  list_set (list_set a 0%nat last) (length a - 1)%nat first
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if all elements in range satisfy a predicate *)
Fixpoint all_range (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && all_range n' f
  end.

Definition swapFirstAndLast_postcond_dec (a result : list Z) : bool :=
  (length result =? length a)%nat &&
  (Z.eqb (list_get result 0%nat 0) (list_get a (length a - 1)%nat 0)) &&
  (Z.eqb (list_get result (length result - 1)%nat 0) (list_get a 0%nat 0)) &&
  (all_range (length result - 2)%nat (fun i => Z.eqb (list_get result (i + 1)%nat 0) (list_get a (i + 1)%nat 0))).
(* !benchmark @end postcond_aux *)

Definition swapFirstAndLast_postcond (a : (list Z)) (result : (list Z)) (h_precond : swapFirstAndLast_precond a) : Prop :=
  (* !benchmark @start postcond *)
  length result = length a /\
  list_get result 0%nat 0 = list_get a (length a - 1)%nat 0 /\
  list_get result (length result - 1)%nat 0 = list_get a 0%nat 0 /\
  (forall i : nat, (i < length result - 2)%nat -> 
    list_get result (i + 1)%nat 0 = list_get a (i + 1)%nat 0)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem swapFirstAndLast_postcond_satisfied (a : (list Z)) (h_precond : swapFirstAndLast_precond a) :
    swapFirstAndLast_postcond a (swapFirstAndLast a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
