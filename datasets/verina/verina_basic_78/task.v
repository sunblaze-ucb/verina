(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition MultipleReturns_precond_dec (x : Z) (y : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition MultipleReturns_precond (x : Z) (y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions needed *)
(* !benchmark @end code_aux *)

Definition MultipleReturns (x : Z) (y : Z) (h_precond : MultipleReturns_precond x y) : (Z  * Z) :=
  (* !benchmark @start code *)
  let more := x + y in
  let less := x - y in
  (more, less)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition MultipleReturns_postcond_dec (x : Z) (y : Z) (result : Z * Z) : bool :=
  let '(r1, r2) := result in
  (r1 =? x + y) && (r2 + y =? x).
(* !benchmark @end postcond_aux *)

Definition MultipleReturns_postcond (x : Z) (y : Z) (result : (Z  * Z)) (h_precond : MultipleReturns_precond x y) : Prop :=
  (* !benchmark @start postcond *)
  fst result = x + y /\ snd result + y = x
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem MultipleReturns_postcond_satisfied (x : Z) (y : Z) (h_precond : MultipleReturns_precond x y) :
    MultipleReturns_postcond x y (MultipleReturns x y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
