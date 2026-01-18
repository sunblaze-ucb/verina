(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Arith.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition cubeSurfaceArea_precond_dec (size : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition cubeSurfaceArea_precond (size : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition cubeSurfaceArea (size : nat) (h_precond : cubeSurfaceArea_precond size) : nat :=
  (* !benchmark @start code *)
  6 * size * size
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition cubeSurfaceArea_postcond_dec (size : nat) (result : nat) : bool :=
  Nat.eqb (result - 6 * size * size) 0 && Nat.eqb (6 * size * size - result) 0.
(* !benchmark @end postcond_aux *)

Definition cubeSurfaceArea_postcond (size : nat) (result : nat) (h_precond : cubeSurfaceArea_precond size) : Prop :=
  (* !benchmark @start postcond *)
  result - 6 * size * size = 0 /\ 6 * size * size - result = 0
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem cubeSurfaceArea_postcond_satisfied (size : nat) (h_precond : cubeSurfaceArea_precond size) :
    cubeSurfaceArea_postcond size (cubeSurfaceArea size h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
