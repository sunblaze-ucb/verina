(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
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
Definition only_once_precond_dec (a : list Z) (key : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition only_once_precond (a : (list Z)) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint only_once_loop (a : list Z) (key : Z) (keyCount : nat) : bool :=
  match a with
  | [] => Nat.eqb keyCount 1%nat
  | val :: rest =>
      let newCount := if Z.eqb val key then (keyCount + 1)%nat else keyCount in
      only_once_loop rest key newCount
  end.
(* !benchmark @end code_aux *)

Definition only_once (a : (list Z)) (key : Z) (h_precond : only_once_precond a key) : bool :=
  (* !benchmark @start code *)
  only_once_loop a key 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_occurrences (a : list Z) (key : Z) : nat :=
  match a with
  | [] => 0%nat
  | x :: xs =>
      if Z.eqb x key then (1 + count_occurrences xs key)%nat
      else count_occurrences xs key
  end.

Definition only_once_postcond_dec (a : list Z) (key : Z) (result : bool) : bool :=
  let cnt := count_occurrences a key in
  let cond1 := if Nat.eqb cnt 1%nat then result else true in
  let cond2 := if Nat.eqb cnt 1%nat then true else negb result in
  andb cond1 cond2.
(* !benchmark @end postcond_aux *)

Definition only_once_postcond (a : (list Z)) (key : Z) (result : bool) (h_precond : only_once_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  ((count_occurrences a key = 1%nat) -> result = true) /\
((count_occurrences a key <> 1%nat) -> result = false)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem only_once_postcond_satisfied (a : (list Z)) (key : Z) (h_precond : only_once_precond a key) :
    only_once_postcond a key (only_once a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
