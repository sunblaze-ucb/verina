(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition hasOppositeSign_precond_dec (a : Z) (b : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition hasOppositeSign_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition hasOppositeSign (a : Z) (b : Z) (h_precond : hasOppositeSign_precond a b) : bool :=
  (* !benchmark @start code *)
  (a * b <? 0)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition hasOppositeSign_postcond_dec (a : Z) (b : Z) (result : bool) : bool :=
  let cond := orb (andb (a <? 0)%Z (b >? 0)%Z) (andb (a >? 0)%Z (b <? 0)%Z) in
  andb (implb cond result) (implb (negb cond) (negb result)).
(* !benchmark @end postcond_aux *)

Definition hasOppositeSign_postcond (a : Z) (b : Z) (result : bool) (h_precond : hasOppositeSign_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (((a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)) -> result = true) /\
(~((a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)) -> result = false)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasOppositeSign_postcond_satisfied (a : Z) (b : Z) (h_precond : hasOppositeSign_precond a b) :
    hasOppositeSign_postcond a b (hasOppositeSign a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
