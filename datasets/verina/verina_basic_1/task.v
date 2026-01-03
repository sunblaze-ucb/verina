(* Coq version of hasOppositeSign benchmark task *)
(* Ground truth sections are initially empty - LLM generates everything *)

Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

(* !benchmark @start import type=solution *)
(* Additional imports can be added here *)
(* !benchmark @end import *)

(* !benchmark @start solution_aux *)
(* Helper definitions for solution can be added here *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Helper definitions for precondition can be added here *)
(* !benchmark @end precond_aux *)

Definition hasOppositeSign_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True  (* TODO: ground truth *)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper definitions for code can be added here *)
(* !benchmark @end code_aux *)

Definition hasOppositeSign (a : Z) (b : Z) (h_precond : hasOppositeSign_precond a b) : bool :=
  (* !benchmark @start code *)
  true  (* TODO: ground truth - should be (a * b <? 0)%Z *)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper definitions for postcondition can be added here *)
(* !benchmark @end postcond_aux *)

Definition hasOppositeSign_postcond (a : Z) (b : Z) (result : bool) (h_precond : hasOppositeSign_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  True  (* TODO: ground truth *)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* Helper lemmas for proof can be added here *)
(* !benchmark @end proof_aux *)

Theorem hasOppositeSign_postcond_satisfied (a : Z) (b : Z) (h_precond : hasOppositeSign_precond a b) :
    hasOppositeSign_postcond a b (hasOppositeSign a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.  (* TODO: ground truth *)
  (* !benchmark @end proof *)
Admitted.
