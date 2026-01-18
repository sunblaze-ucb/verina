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
Require Import Coq.Lists.ListSet.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to remove duplicates from a list *)
Fixpoint eraseDups (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | x :: xs => if existsb (Z.eqb x) xs
               then eraseDups xs
               else x :: eraseDups xs
  end.

(* Helper to compute product of list *)
Fixpoint productList (arr : list Z) : Z :=
  match arr with
  | [] => 1
  | x :: xs => (x * productList xs)%Z
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition uniqueProduct_precond_dec (arr : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition uniqueProduct_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to simulate the loop with a set *)
Fixpoint loop (arr : list Z) (seen : list Z) (product : Z) : Z :=
  match arr with
  | [] => product
  | x :: xs => if existsb (Z.eqb x) seen
               then loop xs seen product
               else loop xs (x :: seen) (product * x)%Z
  end.
(* !benchmark @end code_aux *)

Definition uniqueProduct (arr : (list Z)) (h_precond : uniqueProduct_precond arr) : Z :=
  (* !benchmark @start code *)
  loop arr [] 1
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition uniqueProduct_postcond_dec (arr : list Z) (result : Z) : bool :=
  let expected := productList (eraseDups arr) in
  Z.eqb (result - expected) 0 && Z.eqb (expected - result) 0.
(* !benchmark @end postcond_aux *)

Definition uniqueProduct_postcond (arr : (list Z)) (result : Z) (h_precond : uniqueProduct_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  (result - (productList (eraseDups arr)) = 0)%Z /\
((productList (eraseDups arr)) - result = 0)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem uniqueProduct_postcond_satisfied (arr : (list Z)) (h_precond : uniqueProduct_precond arr) :
    uniqueProduct_postcond arr (uniqueProduct arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
