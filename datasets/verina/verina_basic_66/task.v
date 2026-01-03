(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition ComputeIsEven_precond_dec (x : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition ComputeIsEven_precond (x : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition ComputeIsEven (x : Z) (h_precond : ComputeIsEven_precond x) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ComputeIsEven_postcond_dec (x : Z) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition ComputeIsEven_postcond (x : Z) (result : bool) (h_precond : ComputeIsEven_precond x) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem ComputeIsEven_postcond_satisfied (x : Z) (h_precond : ComputeIsEven_precond x) :
    ComputeIsEven_postcond x (ComputeIsEven x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
