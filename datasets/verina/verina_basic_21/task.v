(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isSublist_precond_dec (sub : list Z) (main : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isSublist_precond (sub : (list Z)) (main : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint check (sub : list Z) (main : list Z) (subLen : nat) (mainLen : nat) (i : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb mainLen (i + subLen) then
        false
      else if list_eq_dec Z.eq_dec sub (firstn subLen (skipn i main)) then
        true
      else if Nat.leb (i + 1) mainLen then
        check sub main subLen mainLen (i + 1) fuel'
      else
        false
  end.
(* !benchmark @end code_aux *)

Definition isSublist (sub : (list Z)) (main : (list Z)) (h_precond : isSublist_precond sub main) : bool :=
  (* !benchmark @start code *)
  let subLen := length sub in
  let mainLen := length main in
  if Nat.ltb mainLen subLen then
    false
  else
    check sub main subLen mainLen 0 mainLen
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isSublist_postcond_dec (sub : list Z) (main : list Z) (result : bool) : bool :=
  result.
(* !benchmark @end postcond_aux *)

Definition isSublist_postcond (sub : (list Z)) (main : (list Z)) (result : bool) (h_precond : isSublist_precond sub main) : Prop :=
  (* !benchmark @start postcond *)
  (exists i, (i + length sub <= length main)%nat /\ sub = firstn (length sub) (skipn i main)) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isSublist_postcond_satisfied (sub : (list Z)) (main : (list Z)) (h_precond : isSublist_precond sub main) :
    isSublist_postcond sub main (isSublist sub main h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
