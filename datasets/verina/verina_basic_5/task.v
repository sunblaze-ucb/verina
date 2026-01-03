(* Coq version of multiply benchmark task *)
(* Base imports - required for task signature *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

(* !benchmark @start import type=task *)
(* Task-level imports - base imports above cover signature types *)
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* Solution-specific imports - none needed for this simple task *)
(* !benchmark @end import *)

(* !benchmark @start solution_aux *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* !benchmark @end precond_aux *)

Definition multiply_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition multiply (a : Z) (b : Z) (h_precond : multiply_precond a b) : Z :=
  (* !benchmark @start code *)
  a * b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* !benchmark @end postcond_aux *)

Definition multiply_postcond (a : Z) (b : Z) (result : Z) (h_precond : multiply_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  result = a * b
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem multiply_postcond_satisfied (a : Z) (b : Z) (h_precond : multiply_precond a b) :
    multiply_postcond a b (multiply a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  unfold multiply, multiply_postcond.
  reflexivity.
  (* !benchmark @end proof *)
Qed.
