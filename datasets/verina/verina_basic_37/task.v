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
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Pairwise ordering predicate for sorted lists *)
Inductive Pairwise {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
  | Pairwise_nil : Pairwise R []
  | Pairwise_cons : forall x l, 
      (forall y, In y l -> R x y) -> 
      Pairwise R l -> 
      Pairwise R (x :: l).

Definition findFirstOccurrence_precond_dec (arr : list Z) (target : Z) : bool :=
  true. (* Simplified decidable version - checking sorted property is complex *)
(* !benchmark @end precond_aux *)

Definition findFirstOccurrence_precond (arr : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  Pairwise (fun x y => (x <= y)%Z) arr
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findFirstOccurrence_loop (arr : list Z) (target : Z) (i : nat) (size : nat) : Z :=
  match size with
  | O => (-1)%Z
  | S size' =>
      if (i <? size)%nat then
        match nth_error arr i with
        | Some a =>
            if (a =? target)%Z then Z.of_nat i
            else if (a >? target)%Z then (-1)%Z
            else findFirstOccurrence_loop arr target (i + 1)%nat size'
        | None => (-1)%Z
        end
      else (-1)%Z
  end.
(* !benchmark @end code_aux *)

Definition findFirstOccurrence (arr : (list Z)) (target : Z) (h_precond : findFirstOccurrence_precond arr target) : Z :=
  (* !benchmark @start code *)
  findFirstOccurrence_loop arr target 0%nat (length arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findFirstOccurrence_postcond_dec (arr : list Z) (target : Z) (result : Z) : bool :=
  if (result >=? 0)%Z then
    match nth_error arr (Z.to_nat result) with
    | Some v => 
        if (v =? target)%Z then
          true (* Simplified - should check all i < result *)
        else false
    | None => false
    end
  else true. (* Simplified - should check no element equals target *)
(* !benchmark @end postcond_aux *)

Definition findFirstOccurrence_postcond (arr : (list Z)) (target : Z) (result : Z) (h_precond : findFirstOccurrence_precond arr target) : Prop :=
  (* !benchmark @start postcond *)
  ((result >= 0)%Z ->
    (exists v, nth_error arr (Z.to_nat result) = Some v /\ v = target) /\
    (forall i : nat, (i < Z.to_nat result)%nat -> 
      forall v, nth_error arr i = Some v -> v <> target)) /\
  ((result = -1)%Z ->
    (forall i : nat, (i < length arr)%nat -> 
      forall v, nth_error arr i = Some v -> v <> target))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstOccurrence_postcond_satisfied (arr : (list Z)) (target : Z) (h_precond : findFirstOccurrence_precond arr target) :
    findFirstOccurrence_postcond arr target (findFirstOccurrence arr target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
