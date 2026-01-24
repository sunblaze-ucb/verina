(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition ComputeAvg_precond (a : Z) (b : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition ComputeAvg (a : Z) (b : Z) : Z :=
  (* !benchmark @start code *)
  (a + b) / 2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition ComputeAvg_postcond (a : Z) (b : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  (2 * result =? a + b - ((a + b) mod 2))%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ComputeAvg_postcond_satisfied (a : Z) (b : Z) :
    ComputeAvg_precond a b = true ->
    ComputeAvg_postcond a b (ComputeAvg a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
