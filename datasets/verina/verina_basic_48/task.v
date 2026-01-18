(* !benchmark @start import type=task *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Arith.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isPerfectSquare_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition isPerfectSquare_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPerfectSquare_check (x : nat) (fuel : nat) (n : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb n (x * x) then false
      else if (x * x =? n)%nat then true
      else isPerfectSquare_check (x + 1) fuel' n
  end.
(* !benchmark @end code_aux *)

Definition isPerfectSquare (n : nat) (h_precond : isPerfectSquare_precond n) : bool :=
  (* !benchmark @start code *)
  if (n =? 0)%nat then true
else isPerfectSquare_check 1 n n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isPerfectSquare_postcond_dec (n : nat) (result : bool) : bool :=
  result.
(* !benchmark @end postcond_aux *)

Definition isPerfectSquare_postcond (n : nat) (result : bool) (h_precond : isPerfectSquare_precond n) : Prop :=
  (* !benchmark @start postcond *)
  result = true <-> exists i : nat, (i * i = n)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPerfectSquare_postcond_satisfied (n : nat) (h_precond : isPerfectSquare_precond n) :
    isPerfectSquare_postcond n (isPerfectSquare n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
