(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Filter function for lists *)
Fixpoint filter_list {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter_list f xs else filter_list f xs
  end.

(* Check if Z is non-zero *)
Definition is_nonzero (z : Z) : bool := negb (Z.eqb z 0).

(* Check if Z is zero *)
Definition is_zero (z : Z) : bool := Z.eqb z 0.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition MoveZeroesToEnd_precond_dec (arr : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition MoveZeroesToEnd_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Find index of first occurrence of element in list *)
Fixpoint index_of {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if eq_dec x y then 0%nat else S (index_of eq_dec x ys)
  end.
(* !benchmark @end code_aux *)

Definition MoveZeroesToEnd (arr : (list Z)) (h_precond : MoveZeroesToEnd_precond arr) : (list Z) :=
  (* !benchmark @start code *)
  let nonZeros := filter_list is_nonzero arr in
let zeros := filter_list is_zero arr in
nonZeros ++ zeros
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Permutation relation - list has same elements *)
Fixpoint count_occ {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if eq_dec x y then S (count_occ eq_dec ys x) else count_occ eq_dec ys x
  end.

Definition is_perm {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) : Prop :=
  forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x.

Definition Z_eq_dec : forall x y : Z, {x = y} + {x <> y}.
Proof. intros. destruct (Z.eq_dec x y); auto. Defined.

(* Helper to convert sumbool to bool *)
Definition sumbool_to_bool {P Q : Prop} (s : {P} + {Q}) : bool :=
  if s then true else false.

(* Decidable version of postcondition *)
Definition MoveZeroesToEnd_postcond_dec (arr result : list Z) : bool :=
  let firstResZeroIdx := index_of Z_eq_dec 0 result in
  let nonZeros := filter_list is_nonzero arr in
  let zeros := filter_list is_zero arr in
  andb (sumbool_to_bool (list_eq_dec Z_eq_dec (firstn firstResZeroIdx result) nonZeros))
       (sumbool_to_bool (list_eq_dec Z_eq_dec (skipn firstResZeroIdx result) zeros)).
(* !benchmark @end postcond_aux *)

Definition MoveZeroesToEnd_postcond (arr : (list Z)) (result : (list Z)) (h_precond : MoveZeroesToEnd_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  let firstResZeroIdx := index_of Z_eq_dec 0 result in
is_perm Z_eq_dec result arr /\
firstn firstResZeroIdx result = filter_list is_nonzero arr /\
skipn firstResZeroIdx result = filter_list is_zero arr
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem MoveZeroesToEnd_postcond_satisfied (arr : (list Z)) (h_precond : MoveZeroesToEnd_precond arr) :
    MoveZeroesToEnd_postcond arr (MoveZeroesToEnd arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
