(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Permutation.
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
Definition insertionSort_precond_dec (xs : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition insertionSort_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (ys : list Z) : list Z :=
  match ys with
  | [] => [x]
  | y :: ys' =>
    if (x <=? y)%Z then
      x :: y :: ys'
    else
      y :: insert x ys'
  end.

Fixpoint sort (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | x :: xs => insert x (sort xs)
  end.
(* !benchmark @end code_aux *)

Definition insertionSort (xs : (list Z)) (h_precond : insertionSort_precond xs) : (list Z) :=
  (* !benchmark @start code *)
  sort xs
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tl => (x <= y)%Z /\ sorted tl
  end.

Fixpoint sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl => (x <=? y)%Z && sorted_dec tl
  end.

Fixpoint pairwise (R : Z -> Z -> Prop) (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: tl => Forall (R x) tl /\ pairwise R tl
  end.

Definition insertionSort_postcond_dec (xs result : list Z) : bool :=
  sorted_dec result.
(* !benchmark @end postcond_aux *)

Definition insertionSort_postcond (xs : (list Z)) (result : (list Z)) (h_precond : insertionSort_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  pairwise Z.le result /\ Permutation xs result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insertionSort_postcond_satisfied (xs : (list Z)) (h_precond : insertionSort_precond xs) :
    insertionSort_postcond xs (insertionSort xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
