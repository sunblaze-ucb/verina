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
Definition Compare_precond_dec (a : Z) (b : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition Compare_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition Compare (a : Z) (b : Z) (h_precond : Compare_precond a b) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Compare_postcond_dec (a : Z) (b : Z) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition Compare_postcond (a : Z) (b : Z) (result : bool) (h_precond : Compare_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem Compare_postcond_satisfied (a : Z) (b : Z) (h_precond : Compare_precond a b) :
    Compare_postcond a b (Compare a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
