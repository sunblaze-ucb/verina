(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition only_once_precond (a : (list Z)) (key : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint only_once_loop (a : list Z) (key : Z) (keyCount : nat) : bool :=
  match a with
  | [] => (keyCount =? 1)%nat
  | x :: xs =>
      let newCount := if (x =? key)%Z then (keyCount + 1)%nat else keyCount in
      only_once_loop xs key newCount
  end.
(* !benchmark @end code_aux *)

Definition only_once (a : (list Z)) (key : Z) : bool :=
  (* !benchmark @start code *)
  only_once_loop a key 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_occurrences (a : list Z) (key : Z) : nat :=
  match a with
  | [] => 0%nat
  | x :: xs =>
      if (x =? key)%Z then (1 + count_occurrences xs key)%nat
      else count_occurrences xs key
  end.
(* !benchmark @end postcond_aux *)

Definition only_once_postcond (a : (list Z)) (key : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  implb ((count_occurrences a key =? 1)%nat) result &&
  implb (negb (count_occurrences a key =? 1)%nat) (negb result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem only_once_postcond_satisfied (a : (list Z)) (key : Z) :
    only_once_precond a key = true ->
    only_once_postcond a key (only_once a key) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
