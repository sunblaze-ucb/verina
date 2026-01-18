(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Nat.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition DivisionFunction_precond_dec (x : nat) (y : nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition DivisionFunction_precond (x : nat) (y : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition divMod (x y : nat) : (Z * Z) :=
  let q : Z := Z.of_nat (x / y) in
  let r : Z := Z.of_nat (Nat.modulo x y) in
  (r, q).
(* !benchmark @end code_aux *)

Definition DivisionFunction (x : nat) (y : nat) (h_precond : DivisionFunction_precond x y) : (Z  * Z) :=
  (* !benchmark @start code *)
  if (y =? 0)%nat then (Z.of_nat x, 0) else divMod x y
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition DivisionFunction_postcond_dec (x : nat) (y : nat) (result : Z * Z) : bool :=
  let '(r, q) := result in
  if (y =? 0)%nat then
    (Z.eqb r (Z.of_nat x)) && (Z.eqb q 0)
  else
    (Z.eqb (q * Z.of_nat y + r) (Z.of_nat x)) &&
    (Z.leb 0 r) && (Z.ltb r (Z.of_nat y)) &&
    (Z.leb 0 q).
(* !benchmark @end postcond_aux *)

Definition DivisionFunction_postcond (x : nat) (y : nat) (result : (Z  * Z)) (h_precond : DivisionFunction_precond x y) : Prop :=
  (* !benchmark @start postcond *)
  let '(r, q) := result in
  ((y = 0%nat) -> r = Z.of_nat x /\ q = 0) /\
  ((y <> 0%nat) -> (q * Z.of_nat y + r = Z.of_nat x) /\ (0 <= r /\ r < Z.of_nat y) /\ (0 <= q))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem DivisionFunction_postcond_satisfied (x : nat) (y : nat) (h_precond : DivisionFunction_precond x y) :
    DivisionFunction_postcond x y (DivisionFunction x y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
