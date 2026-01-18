(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to check if a list is sorted in non-decreasing order *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tail => x <= y /\ is_sorted tail
  end.

Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tail => (x <=? y) && is_sorted_dec tail
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition lastPosition_precond_dec (arr : list Z) (elem : Z) : bool :=
  is_sorted_dec arr.
(* !benchmark @end precond_aux *)

Definition lastPosition_precond (arr : (list Z)) (elem : Z) : Prop :=
  (* !benchmark @start precond *)
  is_sorted arr
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint lastPosition_helper (arr : list Z) (elem : Z) (fuel : nat) (i : nat) (pos : Z) : Z :=
  match fuel with
  | O => pos
  | S fuel' =>
    if (i <? length arr)%nat then
      let a := nth i arr 0 in
      if Z.eqb a elem then
        lastPosition_helper arr elem fuel' (S i) (Z.of_nat i)
      else
        lastPosition_helper arr elem fuel' (S i) pos
    else
      pos
  end.
(* !benchmark @end code_aux *)

Definition lastPosition (arr : (list Z)) (elem : Z) (h_precond : lastPosition_precond arr elem) : Z :=
  (* !benchmark @start code *)
  lastPosition_helper arr elem (length arr) 0%nat (-1)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition lastPosition_postcond_dec (arr : list Z) (elem : Z) (result : Z) : bool :=
  if (result >=? 0) then
    let idx := Z.to_nat result in
    if (idx <? length arr)%nat then
      let elem_at_idx := nth idx arr 0 in
      let tail := skipn (idx + 1)%nat arr in
      Z.eqb elem_at_idx elem && forallb (fun x => negb (Z.eqb x elem)) tail
    else
      false
  else if Z.eqb result (-1) then
    forallb (fun x => negb (Z.eqb x elem)) arr
  else
    false.
(* !benchmark @end postcond_aux *)

Definition lastPosition_postcond (arr : (list Z)) (elem : Z) (result : Z) (h_precond : lastPosition_precond arr elem) : Prop :=
  (* !benchmark @start postcond *)
  ((result >= 0 ->
    (Z.to_nat result < length arr)%nat /\
    nth (Z.to_nat result) arr 0 = elem /\
    Forall (fun x => x <> elem) (skipn (Z.to_nat result + 1)%nat arr)) /\
  (result = -1 -> Forall (fun x => x <> elem) arr))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lastPosition_postcond_satisfied (arr : (list Z)) (elem : Z) (h_precond : lastPosition_precond arr elem) :
    lastPosition_postcond arr elem (lastPosition arr elem h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
