(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to convert Z to nat *)
Definition Z_to_nat (z : Z) : nat :=
  match z with
  | Z0 => 0%nat
  | Zpos p => Pos.to_nat p
  | Zneg _ => 0%nat
  end.

(* Helper function to get element at index with default *)
Fixpoint nth_default {A : Type} (default : A) (l : list A) (n : nat) : A :=
  match n, l with
  | O, [] => default
  | O, x :: _ => x
  | S n', [] => default
  | S n', _ :: tl => nth_default default tl n'
  end.

(* Helper function to set element at index *)
Fixpoint set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match n, l with
  | O, [] => [v]
  | O, _ :: tl => v :: tl
  | S n', [] => [] (* Invalid case - return empty *)
  | S n', hd :: tl => hd :: set_nth tl n' v
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition swap_precond_dec (arr : list Z) (i : Z) (j : Z) : bool :=
  ((i >=? 0)%Z && (j >=? 0)%Z && 
   (Z_to_nat i <? length arr)%nat && 
   (Z_to_nat j <? length arr)%nat)%bool.
(* !benchmark @end precond_aux *)

Definition swap_precond (arr : (list Z)) (i : Z) (j : Z) : Prop :=
  (* !benchmark @start precond *)
  (i >= 0)%Z /\
  (j >= 0)%Z /\
  (Z_to_nat i < length arr)%nat /\
  (Z_to_nat j < length arr)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper functions already defined in SOLUTION_AUX *)
(* !benchmark @end code_aux *)

Definition swap (arr : (list Z)) (i : Z) (j : Z) (h_precond : swap_precond arr i j) : (list Z) :=
  (* !benchmark @start code *)
  let i_nat := Z_to_nat i in
  let j_nat := Z_to_nat j in
  let arr1 := set_nth arr i_nat (nth_default 0%Z arr j_nat) in
  let arr2 := set_nth arr1 j_nat (nth_default 0%Z arr i_nat) in
  arr2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition swap_postcond_dec (arr : list Z) (i : Z) (j : Z) (result : list Z) : bool :=
  let i_nat := Z_to_nat i in
  let j_nat := Z_to_nat j in
  ((nth_default 0%Z result i_nat =? nth_default 0%Z arr j_nat)%Z &&
   (nth_default 0%Z result j_nat =? nth_default 0%Z arr i_nat)%Z)%bool.
(* !benchmark @end postcond_aux *)

Definition swap_postcond (arr : (list Z)) (i : Z) (j : Z) (result : (list Z)) (h_precond : swap_precond arr i j) : Prop :=
  (* !benchmark @start postcond *)
  let i_nat := Z_to_nat i in
  let j_nat := Z_to_nat j in
  (nth_default 0%Z result i_nat = nth_default 0%Z arr j_nat) /\
  (nth_default 0%Z result j_nat = nth_default 0%Z arr i_nat) /\
  (forall (k : nat), (k < length arr)%nat -> k <> i_nat -> k <> j_nat -> 
    nth_default 0%Z result k = nth_default 0%Z arr k)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem swap_postcond_satisfied (arr : (list Z)) (i : Z) (j : Z) (h_precond : swap_precond arr i j) :
    swap_postcond arr i j (swap arr i j h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
