(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition TestArrayElements_precond_dec (a : list Z) (j : nat) : bool :=
  (j <? List.length a)%nat.
(* !benchmark @end precond_aux *)

Definition TestArrayElements_precond (a : (list Z)) (j : nat) : Prop :=
  (* !benchmark @start precond *)
  (j < List.length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint set_at {A : Type} (l : list A) (i : nat) (v : A) : list A :=
  match l with
  | [] => []
  | h :: t =>
    match i with
    | 0%nat => v :: t
    | S i' => h :: set_at t i' v
    end
  end.
(* !benchmark @end code_aux *)

Definition TestArrayElements (a : (list Z)) (j : nat) (h_precond : TestArrayElements_precond a j) : (list Z) :=
  (* !benchmark @start code *)
  set_at a j 60%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: t =>
    match n with
    | 0%nat => h
    | S n' => nth_Z t n' default
    end
  end.

Definition TestArrayElements_postcond_dec (a : list Z) (j : nat) (result : list Z) : bool :=
  (Z.eqb (nth_Z result j 0%Z) 60%Z) &&
  (forallb (fun k => 
    if Nat.eqb k j then true 
    else Z.eqb (nth_Z result k 0%Z) (nth_Z a k 0%Z))
    (seq 0%nat (List.length a))).
(* !benchmark @end postcond_aux *)

Definition TestArrayElements_postcond (a : (list Z)) (j : nat) (result : (list Z)) (h_precond : TestArrayElements_precond a j) : Prop :=
  (* !benchmark @start postcond *)
  (nth_Z result j 0%Z = 60%Z) /\ 
(forall k : nat, (k < List.length a)%nat -> k <> j -> nth_Z result k 0%Z = nth_Z a k 0%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem TestArrayElements_postcond_satisfied (a : (list Z)) (j : nat) (h_precond : TestArrayElements_precond a j) :
    TestArrayElements_postcond a j (TestArrayElements a j h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
