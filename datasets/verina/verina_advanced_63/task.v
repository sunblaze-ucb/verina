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
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Pairwise relation for sorted list *)
Fixpoint Pairwise {A : Type} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
    (Forall (R x) xs) /\ Pairwise R xs
  end.

Definition removeDuplicates_precond_dec (nums : list Z) : bool :=
  let fix check_pairwise (l : list Z) : bool :=
    match l with
    | [] => true
    | x :: xs =>
      let fix check_all (y : Z) (ys : list Z) : bool :=
        match ys with
        | [] => true
        | z :: zs => (y <=? z)%Z && check_all z zs
        end in
      check_all x xs && check_pairwise xs
    end in
  check_pairwise nums.
(* !benchmark @end precond_aux *)

Definition removeDuplicates_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  Pairwise Z.le nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint removeDuplicates_countUniques (prev : Z) (xs : list Z) (k : nat) : nat :=
  match xs with
  | [] => k
  | head :: tail =>
    let isDuplicate := Z.eqb head prev in
    if isDuplicate then
      removeDuplicates_countUniques prev tail k
    else
      let newK := (k + 1)%nat in
      removeDuplicates_countUniques head tail newK
  end.
(* !benchmark @end code_aux *)

Definition removeDuplicates (nums : (list Z)) (h_precond : removeDuplicates_precond nums) : nat :=
  (* !benchmark @start code *)
  match nums with
| [] => 0%nat
| h :: t =>
  let init := h in
  let initCount := 1%nat in
  removeDuplicates_countUniques init t initCount
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint eraseDups (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let rest := eraseDups xs in
    if existsb (Z.eqb x) rest then rest else x :: rest
  end.

Definition removeDuplicates_postcond_dec (nums : list Z) (result : nat) : bool :=
  let unique_len := length (eraseDups nums) in
  Nat.eqb (result - unique_len)%nat 0%nat && Nat.leb unique_len result.
(* !benchmark @end postcond_aux *)

Definition removeDuplicates_postcond (nums : (list Z)) (result : nat) (h_precond : removeDuplicates_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (result - length (eraseDups nums) = 0)%nat /\
(length (eraseDups nums) <= result)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeDuplicates_postcond_satisfied (nums : (list Z)) (h_precond : removeDuplicates_precond nums) :
    removeDuplicates_postcond nums (removeDuplicates nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
