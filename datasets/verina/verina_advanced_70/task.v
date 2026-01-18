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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* additional helper definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_nodup {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~In x xs /\ list_nodup eq_dec xs
  end.

Fixpoint list_all {A : Type} (p : A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => p x /\ list_all p xs
  end.

Definition semiOrderedPermutation_precond_dec (nums : list Z) : bool :=
  let n := length nums in
  (n >? 0)%nat && NoDup_dec Z.eq_dec nums && 
  forallb (fun x => (1 <=? x) && (x <=? Z.of_nat n)) nums.
(* !benchmark @end precond_aux *)

Definition semiOrderedPermutation_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  let n := length nums in
  ((n > 0)%nat /\
  NoDup nums /\
  list_all (fun x => 1 <= x /\ x <= Z.of_nat n) nums)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint idxOf (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: ys => if Z.eqb x y then 0 else 1 + idxOf x ys
  end.
(* !benchmark @end code_aux *)

Definition semiOrderedPermutation (nums : (list Z)) (h_precond : semiOrderedPermutation_precond nums) : Z :=
  (* !benchmark @start code *)
  let lengthList := length nums in
  let numOne : Z := 1 in
  let largestNum : Z := Z.of_nat lengthList in
  let firstIndex := idxOf numOne nums in
  let lastIndex := idxOf largestNum nums in
  let startPosition := 0 in
  let endPosition := Z.of_nat lengthList - 1 in
  let shouldMoveOne := negb (Z.eqb firstIndex startPosition) in
  let shouldMoveLast := negb (Z.eqb lastIndex endPosition) in
  let distanceOne := if shouldMoveOne then firstIndex else 0 in
  let distanceLast := if shouldMoveLast then endPosition - lastIndex else 0 in
  let totalMoves := distanceOne + distanceLast in
  let needAdjustment := firstIndex >? lastIndex in
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves in
  adjustedMoves
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition semiOrderedPermutation_postcond_dec (nums : list Z) (result : Z) : bool :=
  let n := length nums in
  let pos1 := idxOf 1 nums in
  let posn := idxOf (Z.of_nat n) nums in
  if pos1 >? posn then
    Z.eqb (pos1 + Z.of_nat n) (result + 2 + posn)
  else
    Z.eqb (pos1 + Z.of_nat n) (result + 1 + posn).
(* !benchmark @end postcond_aux *)

Definition semiOrderedPermutation_postcond (nums : (list Z)) (result : Z) (h_precond : semiOrderedPermutation_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
  let pos1 := idxOf 1 nums in
  let posn := idxOf (Z.of_nat n) nums in
  if (pos1 >? posn)%Z then
    (pos1 + Z.of_nat n = result + 2 + posn)%Z
  else
    (pos1 + Z.of_nat n = result + 1 + posn)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem semiOrderedPermutation_postcond_satisfied (nums : (list Z)) (h_precond : semiOrderedPermutation_precond nums) :
    semiOrderedPermutation_postcond nums (semiOrderedPermutation nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
