(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No auxiliary type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition ComputeAvg_precond_dec (a : Z) (b : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition ComputeAvg_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions needed *)
(* !benchmark @end code_aux *)

Definition ComputeAvg (a : Z) (b : Z) (h_precond : ComputeAvg_precond a b) : Z :=
  (* !benchmark @start code *)
  (a + b) / 2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ComputeAvg_postcond_dec (a : Z) (b : Z) (result : Z) : bool :=
  (2 * result =? a + b - ((a + b) mod 2))%Z.
(* !benchmark @end postcond_aux *)

Definition ComputeAvg_postcond (a : Z) (b : Z) (result : Z) (h_precond : ComputeAvg_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  2 * result = a + b - ((a + b) mod 2)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ComputeAvg_postcond_satisfied (a : Z) (b : Z) (h_precond : ComputeAvg_precond a b) :
    ComputeAvg_postcond a b (ComputeAvg a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
