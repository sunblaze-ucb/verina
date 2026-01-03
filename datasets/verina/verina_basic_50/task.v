(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition Abs_precond_dec (x : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition Abs_precond (x : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition Abs (x : Z) (h_precond : Abs_precond x) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Abs_postcond_dec (x : Z) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition Abs_postcond (x : Z) (result : Z) (h_precond : Abs_precond x) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem Abs_postcond_satisfied (x : Z) (h_precond : Abs_precond x) :
    Abs_postcond x (Abs x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
