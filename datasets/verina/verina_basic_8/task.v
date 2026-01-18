(* !benchmark @start import type=task *)
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
Definition myMin_precond_dec (a : Z) (b : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition myMin_precond (a : Z) (b : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition myMin (a : Z) (b : Z) (h_precond : myMin_precond a b) : Z :=
  (* !benchmark @start code *)
  if a <=? b then a else b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition myMin_postcond_dec (a : Z) (b : Z) (result : Z) : bool :=
  andb (andb (result <=? a) (result <=? b))
       (orb (result =? a) (result =? b)).
(* !benchmark @end postcond_aux *)

Definition myMin_postcond (a : Z) (b : Z) (result : Z) (h_precond : myMin_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (result <= a /\ result <= b) /\ (result = a \/ result = b)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem myMin_postcond_satisfied (a : Z) (b : Z) (h_precond : myMin_precond a b) :
    myMin_postcond a b (myMin a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
