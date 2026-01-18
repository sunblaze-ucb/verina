(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition isDivisibleBy11_precond_dec (n : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition isDivisibleBy11_precond (n : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition isDivisibleBy11 (n : Z) (h_precond : isDivisibleBy11_precond n) : bool :=
  (* !benchmark @start code *)
  (n mod 11 =? 0)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Definition isDivisibleBy11_postcond_dec (n : Z) (result : bool) : bool :=
  if result then (n mod 11 =? 0)%Z else negb (n mod 11 =? 0)%Z.
(* !benchmark @end postcond_aux *)

Definition isDivisibleBy11_postcond (n : Z) (result : bool) (h_precond : isDivisibleBy11_precond n) : Prop :=
  (* !benchmark @start postcond *)
  (result = true -> exists k : Z, n = 11 * k) /\ (result = false -> forall k : Z, n <> 11 * k)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isDivisibleBy11_postcond_satisfied (n : Z) (h_precond : isDivisibleBy11_precond n) :
    isDivisibleBy11_postcond n (isDivisibleBy11 n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
