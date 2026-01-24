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

Definition DoubleQuadruple_precond (x : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition DoubleQuadruple (x : Z) : (Z  * Z) :=
  (* !benchmark @start code *)
  let a := 2 * x in
  let b := 2 * a in
  (a, b)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition DoubleQuadruple_postcond (x : Z) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  ((fst result) =? 2 * x) && ((snd result) =? 2 * (fst result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem DoubleQuadruple_postcond_satisfied (x : Z) :
    DoubleQuadruple_precond x = true ->
    DoubleQuadruple_postcond x (DoubleQuadruple x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
