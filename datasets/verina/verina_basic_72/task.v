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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition append_precond_dec (a : list Z) (b : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition append_precond (a : (list Z)) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint copy_helper (a : list Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' =>
      match a with
      | [] => []
      | x :: xs => x :: copy_helper xs n'
      end
  end.

Definition copy (a : list Z) : list Z :=
  copy_helper a (length a).
(* !benchmark @end code_aux *)

Definition append (a : (list Z)) (b : Z) (h_precond : append_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let c_initial := copy a in
  let c_full := c_initial ++ [b] in
  c_full
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_indices_match (result : list Z) (a : list Z) (size : nat) : bool :=
  match size with
  | O => true
  | S n =>
      match nth_error result n, nth_error a n with
      | Some r, Some av => if (r =? av)%Z then all_indices_match result a n else false
      | _, _ => false
      end
  end.

Definition append_postcond_dec (a : list Z) (b : Z) (result : list Z) : bool :=
  match nth_error result (length a) with
  | Some elem =>
      (all_indices_match result a (length a)) &&
      (elem =? b)%Z &&
      (Nat.eqb (length result) (length a + 1%nat))
  | None => false
  end.
(* !benchmark @end postcond_aux *)

Definition append_postcond (a : (list Z)) (b : Z) (result : (list Z)) (h_precond : append_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (forall i : nat, (i < length a)%nat -> 
  exists r av, nth_error result i = Some r /\ nth_error a i = Some av /\ r = av) /\
nth_error result (length a) = Some b /\
(length result = length a + 1%nat)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem append_postcond_satisfied (a : (list Z)) (b : Z) (h_precond : append_precond a b) :
    append_postcond a b (append a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
