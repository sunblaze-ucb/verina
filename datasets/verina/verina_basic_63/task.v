(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Reals.
Require Import Rbase.
Open Scope R_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Reals.Rdefinitions.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition Rabs_diff (a b : R) : R :=
  Rabs (a - b).

Definition Rltb (x y : R) : bool :=
  match Rlt_dec x y with
  | left _ => true
  | right _ => false
  end.

Fixpoint nth_default (l : list R) (n : nat) (default : R) : R :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default t n' default
              end
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition has_close_elements_precond (numbers : (list R)) (threshold : R) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint inner_loop (numbers : list R) (threshold : R) (idx idx2 : nat) : bool :=
  match idx2 with
  | O => false
  | S idx2' =>
    let a := nth_default numbers idx2' 0 in
    let b := nth_default numbers idx 0 in
    let d := Rabs_diff a b in
    if Rltb d threshold then true
    else inner_loop numbers threshold idx idx2'
  end.

Fixpoint outer_loop (numbers : list R) (threshold : R) (idx remaining : nat) : bool :=
  match remaining with
  | O => false
  | S rem' =>
    if inner_loop numbers threshold idx idx then true
    else outer_loop numbers threshold (S idx) rem'
  end.
(* !benchmark @end code_aux *)

Definition has_close_elements (numbers : (list R)) (threshold : R) : bool :=
  (* !benchmark @start code *)
  outer_loop numbers threshold 0 (length numbers)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Rgeb (x y : R) : bool :=
  match Rge_dec x y with
  | left _ => true
  | right _ => false
  end.

Fixpoint pairwise_check (l : list R) (threshold : R) : bool :=
  match l with
  | [] => true
  | h :: t => forallb (fun x => Rgeb (Rabs_diff h x) threshold) t && pairwise_check t threshold
  end.
(* !benchmark @end postcond_aux *)

Definition has_close_elements_postcond (numbers : (list R)) (threshold : R) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (negb result) (pairwise_check numbers threshold)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem has_close_elements_postcond_satisfied (numbers : (list R)) (threshold : R) :
    has_close_elements_precond numbers threshold = true ->
    has_close_elements_postcond numbers threshold (has_close_elements numbers threshold) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
