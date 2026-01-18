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
(* Helper function to remove element at index k from list *)
Fixpoint removeAt {A : Type} (l : list A) (k : nat) : list A :=
  match k, l with
  | 0%nat, _ :: tl => tl
  | S k', hd :: tl => hd :: removeAt tl k'
  | _, [] => []
  end.

(* Helper function to get element at index i *)
Fixpoint nth_Z (l : list Z) (i : nat) : Z :=
  match i, l with
  | 0%nat, hd :: _ => hd
  | S i', _ :: tl => nth_Z tl i'
  | _, [] => 0%Z
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition removeElement_precond_dec (s : list Z) (k : nat) : bool :=
  (k <? length s)%nat.
(* !benchmark @end precond_aux *)

Definition removeElement_precond (s : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  (k < length s)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers needed *)
(* !benchmark @end code_aux *)

Definition removeElement (s : (list Z)) (k : nat) (h_precond : removeElement_precond s k) : (list Z) :=
  (* !benchmark @start code *)
  removeAt s k
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition removeElement_postcond_dec (s : list Z) (k : nat) (result : list Z) : bool :=
  let size_check := Nat.eqb (length result) (length s - 1)%nat in
  let before_check := 
    forallb (fun i => Z.eqb (nth_Z result i) (nth_Z s i)) (seq 0 k) in
  let after_check := 
    forallb (fun i => 
      if andb (i <? length result)%nat (k <=? i)%nat
      then Z.eqb (nth_Z result i) (nth_Z s (i + 1)%nat)
      else true) (seq 0 (length result)) in
  andb (andb size_check before_check) after_check.
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (s : (list Z)) (k : nat) (result : (list Z)) (h_precond : removeElement_precond s k) : Prop :=
  (* !benchmark @start postcond *)
  length result = (length s - 1)%nat /\
  (forall i, (i < k)%nat -> nth_Z result i = nth_Z s i) /\
  (forall i, (i < length result)%nat -> (i >= k)%nat -> nth_Z result i = nth_Z s (i + 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (s : (list Z)) (k : nat) (h_precond : removeElement_precond s k) :
    removeElement_postcond s k (removeElement s k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
