(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Inductive Pairwise {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| Pairwise_nil : Pairwise R []
| Pairwise_cons : forall x l, (forall y, In y l -> R x y) -> Pairwise R l -> Pairwise R (x :: l).

Fixpoint pairwise_lt_dec (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <? y) && pairwise_lt_dec xs
    end
  end.

Definition smallestMissing_precond_dec (l : list nat) : bool :=
  pairwise_lt_dec l.
(* !benchmark @end precond_aux *)

Definition smallestMissing_precond (l : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  Pairwise (fun x y => x < y) l
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint search (lst : list nat) (n : nat) : nat :=
  match lst with
  | [] => n
  | x :: xs =>
    let isEqual := Nat.eqb x n in
    let isGreater := Nat.ltb n x in
    let nextCand := n + 1 in
    if isEqual then
      search xs nextCand
    else if isGreater then
      n
    else
      search xs n
  end.
(* !benchmark @end code_aux *)

Definition smallestMissing (l : (list nat)) (h_precond : smallestMissing_precond l) : nat :=
  (* !benchmark @start code *)
  let sortedList := l in
  let result := search sortedList 0%nat in
  result
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nat_in_dec (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => Nat.eqb n x || nat_in_dec n xs
  end.

Fixpoint check_range (n : nat) (l : list nat) : bool :=
  match n with
  | 0%nat => true
  | S n' => nat_in_dec n' l && check_range n' l
  end.

Fixpoint all_less_in_dec (result : nat) (l : list nat) : bool :=
  check_range result l.

Definition smallestMissing_postcond_dec (l : list nat) (result : nat) : bool :=
  negb (nat_in_dec result l) && all_less_in_dec result l.
(* !benchmark @end postcond_aux *)

Definition smallestMissing_postcond (l : (list nat)) (result : nat) (h_precond : smallestMissing_precond l) : Prop :=
  (* !benchmark @start postcond *)
  ~ In result l /\ forall candidate : nat, candidate < result -> In candidate l
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem smallestMissing_postcond_satisfied (l : (list nat)) (h_precond : smallestMissing_precond l) :
    smallestMissing_postcond l (smallestMissing l h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
