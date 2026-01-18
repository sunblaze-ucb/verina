(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition CountLessThan_precond_dec (numbers : list Z) (threshold : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition CountLessThan_precond (numbers : (list Z)) (threshold : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint count_less_than_helper (numbers : list Z) (threshold : Z) (acc : nat) : nat :=
  match numbers with
  | [] => acc
  | n :: rest =>
      let new_acc := if (n <? threshold)%Z then (acc + 1)%nat else acc in
      count_less_than_helper rest threshold new_acc
  end.
(* !benchmark @end code_aux *)

Definition CountLessThan (numbers : (list Z)) (threshold : Z) (h_precond : CountLessThan_precond numbers threshold) : nat :=
  (* !benchmark @start code *)
  count_less_than_helper numbers threshold 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint fold_count (numbers : list Z) (threshold : Z) (acc : nat) : nat :=
  match numbers with
  | [] => acc
  | n :: rest =>
      let new_acc := if (n <? threshold)%Z then (acc + 1)%nat else acc in
      fold_count rest threshold new_acc
  end.

Definition expected_count (numbers : list Z) (threshold : Z) : nat :=
  fold_count numbers threshold 0%nat.

Definition CountLessThan_postcond_dec (numbers : list Z) (threshold : Z) (result : nat) : bool :=
  let expected := expected_count numbers threshold in
  Nat.eqb (result - expected)%nat 0%nat && Nat.eqb (expected - result)%nat 0%nat.
(* !benchmark @end postcond_aux *)

Definition CountLessThan_postcond (numbers : (list Z)) (threshold : Z) (result : nat) (h_precond : CountLessThan_precond numbers threshold) : Prop :=
  (* !benchmark @start postcond *)
  let expected := expected_count numbers threshold in
(result - expected)%nat = 0%nat /\ (expected - result)%nat = 0%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CountLessThan_postcond_satisfied (numbers : (list Z)) (threshold : Z) (h_precond : CountLessThan_precond numbers threshold) :
    CountLessThan_postcond numbers threshold (CountLessThan numbers threshold h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
