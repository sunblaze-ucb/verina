(* !benchmark @start import type=task *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition sumOfFourthPowerOfOddNumbers_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sumOfFourthPowerOfOddNumbers_aux (n : nat) : nat :=
  match n with
  | O => O
  | S n' =>
    let prev := sumOfFourthPowerOfOddNumbers_aux n' in
    let nextOdd := (2 * n' + 1)%nat in
    (prev + nextOdd * nextOdd * nextOdd * nextOdd)%nat
  end.
(* !benchmark @end code_aux *)

Definition sumOfFourthPowerOfOddNumbers (n : nat) : nat :=
  (* !benchmark @start code *)
  sumOfFourthPowerOfOddNumbers_aux n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition sumOfFourthPowerOfOddNumbers_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (15 * result =? n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n))%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfFourthPowerOfOddNumbers_postcond_satisfied (n : nat) :
    sumOfFourthPowerOfOddNumbers_precond n = true ->
    sumOfFourthPowerOfOddNumbers_postcond n (sumOfFourthPowerOfOddNumbers n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
