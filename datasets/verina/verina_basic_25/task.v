(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Reals.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition sumAndAverage_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition sumAndAverage_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition sumAndAverage (n : nat) (h_precond : sumAndAverage_precond n) : (Z  * R) :=
  (* !benchmark @start code *)
  (0%Z, R0)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition sumAndAverage_postcond_dec (n : nat) (result : (Z  * R)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition sumAndAverage_postcond (n : nat) (result : (Z  * R)) (h_precond : sumAndAverage_precond n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem sumAndAverage_postcond_satisfied (n : nat) (h_precond : sumAndAverage_precond n) :
    sumAndAverage_postcond n (sumAndAverage n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.