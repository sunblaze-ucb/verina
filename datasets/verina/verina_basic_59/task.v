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
Definition DoubleQuadruple_precond_dec (x : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition DoubleQuadruple_precond (x : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions *)
(* !benchmark @end code_aux *)

Definition DoubleQuadruple (x : Z) (h_precond : DoubleQuadruple_precond x) : (Z  * Z) :=
  (* !benchmark @start code *)
  let a := 2 * x in
  let b := 2 * a in
  (a, b)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition DoubleQuadruple_postcond_dec (x : Z) (result : Z * Z) : bool :=
  let '(a, b) := result in
  (a =? 2 * x) && (b =? 2 * a).
(* !benchmark @end postcond_aux *)

Definition DoubleQuadruple_postcond (x : Z) (result : (Z  * Z)) (h_precond : DoubleQuadruple_precond x) : Prop :=
  (* !benchmark @start postcond *)
  fst result = 2 * x /\ snd result = 2 * fst result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem DoubleQuadruple_postcond_satisfied (x : Z) (h_precond : DoubleQuadruple_precond x) :
    DoubleQuadruple_postcond x (DoubleQuadruple x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
