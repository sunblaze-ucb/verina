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
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition LinearSearch_precond_dec (a : list Z) (e : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition LinearSearch_precond (a : (list Z)) (e : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint LinearSearch_loop (a : list Z) (e : Z) (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
      if (n <? length a)%nat then
        match nth_error a n with
        | Some v => if (v =? e)%Z then n else LinearSearch_loop a e (n + 1) fuel'
        | None => n
        end
      else n
  end.
(* !benchmark @end code_aux *)

Definition LinearSearch (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) : nat :=
  (* !benchmark @start code *)
  LinearSearch_loop a e 0%nat (length a + 1)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LinearSearch_postcond_dec (a : list Z) (e : Z) (result : nat) : bool :=
  (result <=? length a)%nat &&
  match nth_error a result with
  | Some v => (v =? e)%Z
  | None => (result =? length a)%nat
  end &&
  forallb (fun i => 
    match nth_error a i with
    | Some v => negb (v =? e)%Z
    | None => true
    end) (seq 0 result).
(* !benchmark @end postcond_aux *)

Definition LinearSearch_postcond (a : (list Z)) (e : Z) (result : nat) (h_precond : LinearSearch_precond a e) : Prop :=
  (* !benchmark @start postcond *)
  (result <= length a)%nat /\
(result = length a \/ exists v, nth_error a result = Some v /\ v = e) /\
(forall i, (i < result)%nat -> forall v, nth_error a i = Some v -> v <> e)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch_postcond_satisfied (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) :
    LinearSearch_postcond a e (LinearSearch a e h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
