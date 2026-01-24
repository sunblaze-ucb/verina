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

Definition MultipleReturns_precond (x : Z) (y : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition MultipleReturns (x : Z) (y : Z) : (Z  * Z) :=
  (* !benchmark @start code *)
  let more := x + y in
  let less := x - y in
  (more, less)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition MultipleReturns_postcond (x : Z) (y : Z) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  ((fst result) =? (x + y)) && ((snd result) + y =? x)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem MultipleReturns_postcond_satisfied (x : Z) (y : Z) :
    MultipleReturns_precond x y = true ->
    MultipleReturns_postcond x y (MultipleReturns x y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
