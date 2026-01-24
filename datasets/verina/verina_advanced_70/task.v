(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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
Fixpoint nodup_Z (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (fun y => (x =? y)%Z) xs) && nodup_Z xs
  end.
(* !benchmark @end precond_aux *)

Definition semiOrderedPermutation_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  let n := length nums in
  (1 <=? n)%nat &&
  nodup_Z nums &&
  forallb (fun x => (1 <=? x)%Z && (x <=? Z.of_nat n)%Z) nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint idxOf_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then O else S (idxOf_Z x t)
  end.
(* !benchmark @end code_aux *)

Definition semiOrderedPermutation (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  let lengthList := length nums in
  let numOne := 1%Z in
  let largestNum := Z.of_nat lengthList in
  let firstIndex := idxOf_Z numOne nums in
  let lastIndex := idxOf_Z largestNum nums in
  let startPosition := O in
  let endPosition := (lengthList - 1)%nat in
  let shouldMoveOne := negb (firstIndex =? startPosition)%nat in
  let shouldMoveLast := negb (lastIndex =? endPosition)%nat in
  let distanceOne := if shouldMoveOne then Z.of_nat firstIndex else 0%Z in
  let distanceLast := if shouldMoveLast then Z.of_nat endPosition - Z.of_nat lastIndex else 0%Z in
  let totalMoves := distanceOne + distanceLast in
  let needAdjustment := (lastIndex <? firstIndex)%nat in
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves in
  adjustedMoves
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint idxOf_Z_post (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then O else S (idxOf_Z_post x t)
  end.
(* !benchmark @end postcond_aux *)

Definition semiOrderedPermutation_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let n := length nums in
  let pos1 := idxOf_Z_post 1%Z nums in
  let posn := idxOf_Z_post (Z.of_nat n) nums in
  if (posn <? pos1)%nat then
    (Z.of_nat pos1 + Z.of_nat n =? result + 2 + Z.of_nat posn)%Z
  else
    (Z.of_nat pos1 + Z.of_nat n =? result + 1 + Z.of_nat posn)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem semiOrderedPermutation_postcond_satisfied (nums : (list Z)) :
    semiOrderedPermutation_precond nums = true ->
    semiOrderedPermutation_postcond nums (semiOrderedPermutation nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
