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
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition FindEvenNumbers_precond_dec (arr : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition FindEvenNumbers_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Fixpoint filter_even_loop (lst : list Z) (acc : list Z) : list Z :=
  match lst with
  | [] => acc
  | x :: xs =>
      if isEven x then
        filter_even_loop xs (acc ++ [x])
      else
        filter_even_loop xs acc
  end.
(* !benchmark @end code_aux *)

Definition FindEvenNumbers (arr : (list Z)) (h_precond : FindEvenNumbers_precond arr) : (list Z) :=
  (* !benchmark @start code *)
  filter_even_loop arr []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint all_even (lst : list Z) : Prop :=
  match lst with
  | [] => True
  | x :: xs => isEven x = true /\ all_even xs
  end.

Fixpoint all_even_dec (lst : list Z) : bool :=
  match lst with
  | [] => true
  | x :: xs => andb (isEven x) (all_even_dec xs)
  end.

Inductive Sublist {A : Type} : list A -> list A -> Prop :=
  | sublist_nil : forall l, Sublist [] l
  | sublist_cons : forall x l1 l2, Sublist l1 l2 -> Sublist l1 (x :: l2)
  | sublist_cons_eq : forall x l1 l2, Sublist l1 l2 -> Sublist (x :: l1) (x :: l2).

Fixpoint countP (f : Z -> bool) (lst : list Z) : nat :=
  match lst with
  | [] => 0%nat
  | x :: xs => if f x then (1 + countP f xs)%nat else countP f xs
  end.

Definition FindEvenNumbers_postcond_dec (arr : list Z) (result : list Z) : bool :=
  andb (all_even_dec result) (Nat.eqb (length result) (countP isEven arr)).
(* !benchmark @end postcond_aux *)

Definition FindEvenNumbers_postcond (arr : (list Z)) (result : (list Z)) (h_precond : FindEvenNumbers_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  all_even result /\
  Sublist result arr /\
  length result = countP isEven arr
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem FindEvenNumbers_postcond_satisfied (arr : (list Z)) (h_precond : FindEvenNumbers_precond arr) :
    FindEvenNumbers_postcond arr (FindEvenNumbers arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
