(* !benchmark @start import type=task *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
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
(* precondition helpers including _dec version, complete definitions *)
Definition ifPowerOfFour_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition ifPowerOfFour_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint ifPowerOfFour_helper (n : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match n with
    | O => false
    | S m =>
      match m with
      | O => true
      | S l =>
        let n' := l + 2 in
        if Nat.eqb (Nat.modulo n' 4) 0
        then ifPowerOfFour_helper (Nat.div n' 4) fuel'
        else false
      end
    end
  end.
(* !benchmark @end code_aux *)

Definition ifPowerOfFour (n : nat) (h_precond : ifPowerOfFour_precond n) : bool :=
  (* !benchmark @start code *)
  ifPowerOfFour_helper n n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Definition ifPowerOfFour_postcond_dec (n : nat) (result : bool) : bool :=
  result.
(* !benchmark @end postcond_aux *)

Definition ifPowerOfFour_postcond (n : nat) (result : bool) (h_precond : ifPowerOfFour_precond n) : Prop :=
  (* !benchmark @start postcond *)
  result = true <-> (exists m : nat, n = 4 ^ m)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ifPowerOfFour_postcond_satisfied (n : nat) (h_precond : ifPowerOfFour_precond n) :
    ifPowerOfFour_postcond n (ifPowerOfFour n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
