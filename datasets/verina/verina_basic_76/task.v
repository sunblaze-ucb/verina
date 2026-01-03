(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition myMin_precond_dec (x : Z) (y : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition myMin_precond (x : Z) (y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition myMin (x : Z) (y : Z) (h_precond : myMin_precond x y) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition myMin_postcond_dec (x : Z) (y : Z) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition myMin_postcond (x : Z) (y : Z) (result : Z) (h_precond : myMin_precond x y) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem myMin_postcond_satisfied (x : Z) (y : Z) (h_precond : myMin_precond x y) :
    myMin_postcond x y (myMin x y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
