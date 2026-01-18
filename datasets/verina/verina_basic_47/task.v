(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition arraySum_precond_dec (a : list Z) : bool :=
  (length a >? 0)%nat.
(* !benchmark @end precond_aux *)

Definition arraySum_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: xs => (x + list_sum xs)%Z
  end.
(* !benchmark @end code_aux *)

Definition arraySum (a : (list Z)) (h_precond : arraySum_precond a) : Z :=
  (* !benchmark @start code *)
  list_sum a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sumTo (a : list Z) (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S n' => (sumTo a n' + nth n' a 0%Z)%Z
  end.

Definition arraySum_postcond_dec (a : list Z) (result : Z) : bool :=
  let sum := sumTo a (length a) in
  Z.eqb (result - sum)%Z 0%Z && (result >=? sum)%Z.
(* !benchmark @end postcond_aux *)

Definition arraySum_postcond (a : (list Z)) (result : Z) (h_precond : arraySum_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (result - sumTo a (length a) = 0)%Z /\
(result >= sumTo a (length a))%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arraySum_postcond_satisfied (a : (list Z)) (h_precond : arraySum_precond a) :
    arraySum_postcond a (arraySum a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
