(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition removeElement_precond_dec (lst : list nat) (target : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition removeElement_precond (lst : (list nat)) (target : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint removeElement_helper (lst : list nat) (target : nat) : list nat :=
  match lst with
  | [] => []
  | x :: xs =>
      let rest := removeElement_helper xs target in
      if Nat.eqb x target then rest else x :: rest
  end.
(* !benchmark @end code_aux *)

Definition removeElement (lst : (list nat)) (target : nat) (h_precond : removeElement_precond lst target) : (list nat) :=
  (* !benchmark @start code *)
  removeElement_helper lst target
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint zipWithIndex {A : Type} (l : list A) (start : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, start) :: zipWithIndex xs (S start)
  end.

Definition zipIdx {A : Type} (l : list A) : list (A * nat) :=
  zipWithIndex l 0%nat.

Fixpoint all_pairs (l : list (nat * nat)) (f : nat -> nat -> bool) : bool :=
  match l with
  | [] => true
  | (x, i) :: xs => andb (f x i) (all_pairs xs f)
  end.

Fixpoint nth_option {A : Type} (l : list A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | x :: _, 0%nat => Some x
  | _ :: xs, S n' => nth_option xs n'
  end.

Definition removeElement_postcond_dec (lst : list nat) (target : nat) (result : list nat) : bool :=
  let lst' := filter (fun x => negb (Nat.eqb x target)) lst in
  andb
    (all_pairs (zipIdx result) (fun x i =>
      match nth_option lst' i with
      | Some y => Nat.eqb x y
      | None => false
      end))
    (Nat.eqb (length result) (length lst')).
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (lst : (list nat)) (target : nat) (result : (list nat)) (h_precond : removeElement_precond lst target) : Prop :=
  (* !benchmark @start postcond *)
  let lst' := filter (fun x => negb (Nat.eqb x target)) lst in
  (forall i x, nth_option result i = Some x ->
    nth_option lst' i = Some x) /\
  length result = length lst'
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (lst : (list nat)) (target : nat) (h_precond : removeElement_precond lst target) :
    removeElement_postcond lst target (removeElement lst target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
