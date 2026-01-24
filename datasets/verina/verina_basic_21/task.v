(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%Z && list_Z_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition isSublist_precond (sub : (list Z)) (main : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint check_sublist (sub : list Z) (main : list Z) (subLen : nat) (mainLen : nat) (i : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (mainLen <? i + subLen)%nat then
      false
    else if list_Z_eqb sub (firstn subLen (skipn i main)) then
      true
    else if (i + 1 <=? mainLen)%nat then
      check_sublist sub main subLen mainLen (i + 1)%nat fuel'
    else
      false
  end.
(* !benchmark @end code_aux *)

Definition isSublist (sub : (list Z)) (main : (list Z)) : bool :=
  (* !benchmark @start code *)
  let subLen := length sub in
  let mainLen := length main in
  if (mainLen <? subLen)%nat then
    false
  else
    check_sublist sub main subLen mainLen 0%nat (mainLen + 1)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint exists_index_check (sub : list Z) (main : list Z) (subLen : nat) (mainLen : nat) (i : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (i + subLen <=? mainLen)%nat && list_Z_eqb sub (firstn subLen (skipn i main)) then
      true
    else
      exists_index_check sub main subLen mainLen (i + 1)%nat fuel'
  end.

Definition exists_sublist_at (sub : list Z) (main : list Z) : bool :=
  let subLen := length sub in
  let mainLen := length main in
  exists_index_check sub main subLen mainLen 0%nat (mainLen + 1)%nat.
(* !benchmark @end postcond_aux *)

Definition isSublist_postcond (sub : (list Z)) (main : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (exists_sublist_at sub main) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isSublist_postcond_satisfied (sub : (list Z)) (main : (list Z)) :
    isSublist_precond sub main = true ->
    isSublist_postcond sub main (isSublist sub main) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
