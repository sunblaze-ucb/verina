(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Arith.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution-level helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition CalSum_precond_dec (N : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition CalSum_precond (N : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + loop n'
  end.
(* !benchmark @end code_aux *)

Definition CalSum (N : nat) (h_precond : CalSum_precond N) : nat :=
  (* !benchmark @start code *)
  loop N
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition CalSum_postcond_dec (N : nat) (result : nat) : bool :=
  Nat.eqb (2 * result) (N * (N + 1)).
(* !benchmark @end postcond_aux *)

Definition CalSum_postcond (N : nat) (result : nat) (h_precond : CalSum_precond N) : Prop :=
  (* !benchmark @start postcond *)
  2 * result = N * (N + 1)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CalSum_postcond_satisfied (N : nat) (h_precond : CalSum_precond N) :
    CalSum_postcond N (CalSum N h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
