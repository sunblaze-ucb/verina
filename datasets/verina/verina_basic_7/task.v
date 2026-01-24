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

Definition sumOfSquaresOfFirstNOddNumbers_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (k : nat) (sum : nat) : nat :=
  match k with
  | O => sum
  | S k' => 
    let odd := 2 * k' + 1 in
    loop k' (sum + odd * odd)
  end.
(* !benchmark @end code_aux *)

Definition sumOfSquaresOfFirstNOddNumbers (n : nat) : nat :=
  (* !benchmark @start code *)
  loop n 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition sumOfSquaresOfFirstNOddNumbers_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result =? (n * (2 * n - 1) * (2 * n + 1)) / 3)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfSquaresOfFirstNOddNumbers_postcond_satisfied (n : nat) :
    sumOfSquaresOfFirstNOddNumbers_precond n = true ->
    sumOfSquaresOfFirstNOddNumbers_postcond n (sumOfSquaresOfFirstNOddNumbers n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
