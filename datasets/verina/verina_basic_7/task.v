(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Arith.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition sumOfSquaresOfFirstNOddNumbers_precond_dec (n : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition sumOfSquaresOfFirstNOddNumbers_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sumOfSquaresOfFirstNOddNumbers_loop (k : nat) (sum : nat) : nat :=
  match k with
  | O => sum
  | S k' => sumOfSquaresOfFirstNOddNumbers_loop k' (sum + (2 * k - 1) * (2 * k - 1))
  end.
(* !benchmark @end code_aux *)

Definition sumOfSquaresOfFirstNOddNumbers (n : nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) : nat :=
  (* !benchmark @start code *)
  sumOfSquaresOfFirstNOddNumbers_loop n 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition sumOfSquaresOfFirstNOddNumbers_postcond_dec (n : nat) (result : nat) : bool :=
  Nat.eqb (result - (n * (2 * n - 1) * (2 * n + 1)) / 3) 0 &&
  Nat.eqb ((n * (2 * n - 1) * (2 * n + 1)) / 3 - result) 0.
(* !benchmark @end postcond_aux *)

Definition sumOfSquaresOfFirstNOddNumbers_postcond (n : nat) (result : nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) : Prop :=
  (* !benchmark @start postcond *)
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 /\
(n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfSquaresOfFirstNOddNumbers_postcond_satisfied (n : nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond n) :
    sumOfSquaresOfFirstNOddNumbers_postcond n (sumOfSquaresOfFirstNOddNumbers n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
