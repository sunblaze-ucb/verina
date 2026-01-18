(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition multiply_precond_dec (a : Z) (b : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition multiply_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions *)
(* !benchmark @end code_aux *)

Definition multiply (a : Z) (b : Z) (h_precond : multiply_precond a b) : Z :=
  (* !benchmark @start code *)
  (a * b)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition multiply_postcond_dec (a : Z) (b : Z) (result : Z) : bool :=
  ((result - a * b) =? 0)%Z && ((a * b - result) =? 0)%Z.
(* !benchmark @end postcond_aux *)

Definition multiply_postcond (a : Z) (b : Z) (result : Z) (h_precond : multiply_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (result - a * b = 0)%Z /\ (a * b - result = 0)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem multiply_postcond_satisfied (a : Z) (b : Z) (h_precond : multiply_precond a b) :
    multiply_postcond a b (multiply a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
