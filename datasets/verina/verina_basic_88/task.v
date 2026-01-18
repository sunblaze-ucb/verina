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
Require Import Bool.

Definition ToArray_precond_dec (xs : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition ToArray_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition ToArray (xs : (list Z)) (h_precond : ToArray_precond xs) : (list Z) :=
  (* !benchmark @start code *)
  xs
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Bool.

Definition ToArray_postcond_dec (xs : list Z) (result : list Z) : bool :=
  andb (Nat.eqb (length result) (length xs))
  ((fix check_elements (i : nat) : bool :=
    match i with
    | O => true
    | S i' => 
        match (nth_error xs i'), (nth_error result i') with
        | Some x, Some r => andb (Z.eqb x r) (check_elements i')
        | None, None => check_elements i'
        | _, _ => false
        end
    end) (length xs)).
(* !benchmark @end postcond_aux *)

Definition ToArray_postcond (xs : (list Z)) (result : (list Z)) (h_precond : ToArray_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  length result = length xs /\ forall (i : nat), (i < length xs)%nat -> nth i result 0%Z = nth i xs 0%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ToArray_postcond_satisfied (xs : (list Z)) (h_precond : ToArray_precond xs) :
    ToArray_postcond xs (ToArray xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
