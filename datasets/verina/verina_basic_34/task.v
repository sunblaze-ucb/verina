(* !benchmark @start import type=task *)
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
(* precondition helpers including _dec version, complete definitions *)
Require Import Bool.
Definition findEvenNumbers_precond_dec (arr : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition findEvenNumbers_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Fixpoint filter_even (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if isEven x then x :: filter_even xs else filter_even xs
  end.
(* !benchmark @end code_aux *)

Definition findEvenNumbers (arr : (list Z)) (h_precond : findEvenNumbers_precond arr) : (list Z) :=
  (* !benchmark @start code *)
  filter_even arr
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Bool.
Open Scope bool_scope.

Fixpoint list_mem {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eq_dec x y then true else list_mem eq_dec x ys
  end.

Fixpoint indexOf {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if eq_dec x y then 0%nat else S (indexOf eq_dec x ys)
  end.

Definition findEvenNumbers_postcond_dec (arr : list Z) (result : list Z) : bool :=
  forallb (fun x => isEven x && list_mem Z.eq_dec x arr) result &&
  forallb (fun x => if isEven x then list_mem Z.eq_dec x result else true) arr.
(* !benchmark @end postcond_aux *)

Definition findEvenNumbers_postcond (arr : (list Z)) (result : (list Z)) (h_precond : findEvenNumbers_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  (forall x, In x result -> isEven x = true /\ In x arr) /\
(forall x, In x arr -> isEven x = true -> In x result) /\
(forall x y, In x arr -> In y arr ->
  isEven x = true -> isEven y = true ->
  (indexOf Z.eq_dec x arr <= indexOf Z.eq_dec y arr)%nat ->
  (indexOf Z.eq_dec x result <= indexOf Z.eq_dec y result)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findEvenNumbers_postcond_satisfied (arr : (list Z)) (h_precond : findEvenNumbers_precond arr) :
    findEvenNumbers_postcond arr (findEvenNumbers arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
