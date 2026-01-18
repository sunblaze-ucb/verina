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
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint NoDup_dec {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => if in_dec eq_dec x xs then false else NoDup_dec eq_dec xs
  end.

Definition minimumRightShifts_precond_dec (nums : list Z) : bool :=
  NoDup_dec Z.eq_dec nums.
(* !benchmark @end precond_aux *)

Definition minimumRightShifts_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  NoDup nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint isSortedAux (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => if (x <=? y)%Z then isSortedAux (y :: xs) else false
  end.

Definition rightShiftOnce (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | last :: revInit => last :: rev revInit
  end.

Fixpoint checkShifts (n shifts_count : nat) (current_list : list Z) : Z :=
  match n - shifts_count with
  | O => (-1)%Z
  | S _ =>
      if (shifts_count >=? n)%nat then (-1)%Z
      else if isSortedAux current_list then Z.of_nat shifts_count
      else checkShifts n (shifts_count + 1)%nat (rightShiftOnce current_list)
  end.
(* !benchmark @end code_aux *)

Definition minimumRightShifts (nums : (list Z)) (h_precond : minimumRightShifts_precond nums) : Z :=
  (* !benchmark @start code *)
  let n := length nums in
if (n <=? 1)%nat then 0%Z
else if isSortedAux nums then 0%Z
else checkShifts n 1%nat (rightShiftOnce nums)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint Pairwise_le (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: y :: xs => (x <= y)%Z /\ Pairwise_le (y :: xs)
  end.

Definition isSorted (l : list Z) : Prop := Pairwise_le l.

Fixpoint rotate_right (k : nat) (l : list Z) : list Z :=
  match k with
  | O => l
  | S k' => rotate_right k' (rightShiftOnce l)
  end.

Definition rightShift (k : nat) (l : list Z) : list Z := rotate_right k l.

Fixpoint all_shifts_unsorted (n j : nat) (nums : list Z) : Prop :=
  match j with
  | O => True
  | S j' => ~isSorted (rightShift j' nums) /\ all_shifts_unsorted n j' nums
  end.

Fixpoint Pairwise_le_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => if (x <=? y)%Z then Pairwise_le_dec (y :: xs) else false
  end.

Definition isSorted_dec (l : list Z) : bool := Pairwise_le_dec l.

Fixpoint all_shifts_unsorted_dec (j : nat) (nums : list Z) : bool :=
  match j with
  | O => true
  | S j' => negb (isSorted_dec (rightShift j' nums)) && all_shifts_unsorted_dec j' nums
  end.

Definition minimumRightShifts_postcond_dec (nums : list Z) (result : Z) : bool :=
  let n := length nums in
  if (n <=? 1)%nat then (result =? 0)%Z
  else
    ((result >=? 0)%Z && (result <? Z.of_nat n)%Z &&
     isSorted_dec (rightShift (Z.to_nat result) nums) &&
     all_shifts_unsorted_dec (Z.to_nat result) nums)
    ||
    ((result =? -1)%Z && all_shifts_unsorted_dec n nums).
(* !benchmark @end postcond_aux *)

Definition minimumRightShifts_postcond (nums : (list Z)) (result : Z) (h_precond : minimumRightShifts_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
if (n <=? 1)%nat then result = 0%Z
else
  ((result >= 0)%Z /\
   (result < Z.of_nat n)%Z /\
   isSorted (rightShift (Z.to_nat result) nums) /\
   all_shifts_unsorted n (Z.to_nat result) nums)
  \/
  (result = (-1)%Z /\
   all_shifts_unsorted n n nums)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minimumRightShifts_postcond_satisfied (nums : (list Z)) (h_precond : minimumRightShifts_precond nums) :
    minimumRightShifts_postcond nums (minimumRightShifts nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
