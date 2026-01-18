(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition reverse_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition reverse_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function not actually used in main implementation *)
(* Removed broken reverse_core since it's not used *)
(* !benchmark @end code_aux *)

Definition reverse (a : (list Z)) (h_precond : reverse_precond a) : (list Z) :=
  (* !benchmark @start code *)
  rev a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition reverse_postcond_dec (a : list Z) (result : list Z) : bool :=
  (Nat.eqb (length result) (length a)) &&
  (forallb (fun i => 
    match nth_error result i, nth_error a (length a - 1%nat - i)%nat with
    | Some ri, Some ai => Z.eqb ri ai
    | _, _ => false
    end) (seq 0 (length a))).
(* !benchmark @end postcond_aux *)

Definition reverse_postcond (a : (list Z)) (result : (list Z)) (h_precond : reverse_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length a)%nat /\ (forall i : nat, (i < length a)%nat -> 
  exists ri ai, nth_error result i = Some ri /\ 
                nth_error a (length a - 1%nat - i)%nat = Some ai /\
                ri = ai)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverse_postcond_satisfied (a : (list Z)) (h_precond : reverse_precond a) :
    reverse_postcond a (reverse a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
