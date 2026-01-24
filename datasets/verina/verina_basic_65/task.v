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

Definition SquareRoot_precond (N : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint boundedLoop (bound : nat) (r : nat) (N : nat) : nat :=
  match bound with
  | O => r
  | S bound' =>
      if ((r + 1) * (r + 1) <=? N)%nat then
        boundedLoop bound' (r + 1)%nat N
      else
        r
  end.
(* !benchmark @end code_aux *)

Definition SquareRoot (N : nat) : nat :=
  (* !benchmark @start code *)
  boundedLoop (N + 1)%nat O N
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition SquareRoot_postcond (N : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((result * result <=? N)%nat && (N <? (result + 1) * (result + 1))%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SquareRoot_postcond_satisfied (N : nat) :
    SquareRoot_precond N = true ->
    SquareRoot_postcond N (SquareRoot N) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
