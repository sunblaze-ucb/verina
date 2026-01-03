(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition MultipleReturns_precond_dec (x : Z) (y : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition MultipleReturns_precond (x : Z) (y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition MultipleReturns (x : Z) (y : Z) (h_precond : MultipleReturns_precond x y) : (Z  * Z) :=
  (* !benchmark @start code *)
  (0%Z, 0%Z)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition MultipleReturns_postcond_dec (x : Z) (y : Z) (result : (Z  * Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition MultipleReturns_postcond (x : Z) (y : Z) (result : (Z  * Z)) (h_precond : MultipleReturns_precond x y) : Prop :=
  (* !benchmark @start postcond *)
  True
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