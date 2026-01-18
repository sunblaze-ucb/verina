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
(* precondition helpers including _dec version, complete definitions *)
Definition sumOfFourthPowerOfOddNumbers_precond_dec (n : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition sumOfFourthPowerOfOddNumbers_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition sumOfFourthPowerOfOddNumbers (n : nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond n) : nat :=
  (* !benchmark @start code *)
  (fix f (m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' =>
    let prev := f m' in
    let nextOdd := 2 * m' + 1 in
    prev + (nextOdd * nextOdd * nextOdd * nextOdd)
  end) n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Definition sumOfFourthPowerOfOddNumbers_postcond_dec (n result : nat) : bool :=
  Nat.eqb (15 * result) (n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n)).
(* !benchmark @end postcond_aux *)

Definition sumOfFourthPowerOfOddNumbers_postcond (n : nat) (result : nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond n) : Prop :=
  (* !benchmark @start postcond *)
  15 * result = n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfFourthPowerOfOddNumbers_postcond_satisfied (n : nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond n) :
    sumOfFourthPowerOfOddNumbers_postcond n (sumOfFourthPowerOfOddNumbers n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
