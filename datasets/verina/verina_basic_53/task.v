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

Definition CalSum_precond (N : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n + loop n'
  end.
(* !benchmark @end code_aux *)

Definition CalSum (N : nat) : nat :=
  (* !benchmark @start code *)
  loop N
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition CalSum_postcond (N : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (2 * result =? N * (N + 1))%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CalSum_postcond_satisfied (N : nat) :
    CalSum_precond N = true ->
    CalSum_postcond N (CalSum N) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
