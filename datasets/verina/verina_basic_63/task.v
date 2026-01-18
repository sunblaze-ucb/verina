(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Reals.
Open Scope R_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Reals.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.ROrderedType.
Open Scope R_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint all_valid_floats (numbers : list R) : Prop :=
  match numbers with
  | [] => True
  | x :: xs => True /\ all_valid_floats xs
  end.

Fixpoint all_valid_floats_dec (numbers : list R) : bool :=
  match numbers with
  | [] => true
  | x :: xs => all_valid_floats_dec xs
  end.

Definition has_close_elements_precond_dec (numbers : list R) (threshold : R) : bool :=
  match Rge_dec threshold 0 with
  | left _ => all_valid_floats_dec numbers
  | right _ => false
  end.
(* !benchmark @end precond_aux *)

Definition has_close_elements_precond (numbers : (list R)) (threshold : R) : Prop :=
  (* !benchmark @start precond *)
  threshold >= 0 /\ all_valid_floats numbers
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition absDiff (a b : R) : R :=
  Rabs (a - b).

Definition Rlt_dec (x y : R) : bool :=
  match Rlt_le_dec x y with
  | left _ => true
  | right _ => false
  end.

Fixpoint inner (numbers : list R) (idx idx2 : nat) (threshold : R) : bool :=
  match idx2 with
  | O => false
  | S idx2' =>
      if (idx2' <? idx)%nat then
        let a := nth idx2' numbers 0 in
        let b := nth idx numbers 0 in
        let d := absDiff a b in
        if Rlt_dec d threshold then true
        else inner numbers idx idx2' threshold
      else false
  end.

Fixpoint outer (numbers : list R) (idx len : nat) (threshold : R) : bool :=
  match len with
  | O => false
  | S len' =>
      if (idx <? length numbers)%nat then
        if inner numbers idx idx threshold then true
        else outer numbers (S idx) len' threshold
      else false
  end.
(* !benchmark @end code_aux *)

Definition has_close_elements (numbers : (list R)) (threshold : R) (h_precond : has_close_elements_precond numbers threshold) : bool :=
  (* !benchmark @start code *)
  outer numbers 0%nat (length numbers) threshold
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Inductive Pairwise {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
  | Pairwise_nil : Pairwise R []
  | Pairwise_cons : forall x l, 
      Forall (R x) l -> Pairwise R l -> Pairwise R (x :: l).

Definition Rge_dec_bool (x y : R) : bool :=
  match Rge_dec x y with
  | left _ => true
  | right _ => false
  end.

Fixpoint forall_pairwise_aux (numbers : list R) (threshold : R) (x : R) (rest : list R) : bool :=
  match rest with
  | [] => true
  | y :: ys => Rge_dec_bool (absDiff x y) threshold && forall_pairwise_aux numbers threshold x ys
  end.

Fixpoint pairwise_check (numbers : list R) (threshold : R) : bool :=
  match numbers with
  | [] => true
  | x :: xs => forall_pairwise_aux numbers threshold x xs && pairwise_check xs threshold
  end.

Definition has_close_elements_postcond_dec (numbers : list R) (threshold : R) (result : bool) : bool :=
  if result then negb (pairwise_check numbers threshold)
  else pairwise_check numbers threshold.
(* !benchmark @end postcond_aux *)

Definition has_close_elements_postcond (numbers : (list R)) (threshold : R) (result : bool) (h_precond : has_close_elements_precond numbers threshold) : Prop :=
  (* !benchmark @start postcond *)
  negb result = true <-> Pairwise (fun a b => absDiff a b >= threshold) numbers
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem has_close_elements_postcond_satisfied (numbers : (list R)) (threshold : R) (h_precond : has_close_elements_precond numbers threshold) :
    has_close_elements_postcond numbers threshold (has_close_elements numbers threshold h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
