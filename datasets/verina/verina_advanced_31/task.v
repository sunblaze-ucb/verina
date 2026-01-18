(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
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
(* precondition helpers including _dec version, complete definitions *)
Definition longestIncreasingSubseqLength_precond_dec (xs : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubseqLength_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Generate all subsequences *)
Fixpoint subsequences {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let subs := subsequences xs' in
    subs ++ (map (fun s => x :: s) subs)
  end.

(* Check if a list is strictly increasing *)
Fixpoint isStrictlyIncreasing (xs : list Z) : bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: xs' => 
    match xs' with
    | [] => true
    | y :: rest => if (x <? y)%Z then isStrictlyIncreasing xs' else false
    end
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubseqLength (xs : (list Z)) (h_precond : longestIncreasingSubseqLength_precond xs) : nat :=
  (* !benchmark @start code *)
  let subs := subsequences xs in
let increasing := filter isStrictlyIncreasing subs in
fold_left (fun acc s => Nat.max acc (length s)) increasing 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check Pairwise (< ·) for a list *)
Fixpoint isPairwiseLess (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: l' => 
    match l' with
    | [] => true
    | y :: rest => if (x <? y)%Z then isPairwiseLess l' else false
    end
  end.

(* Generate all subsequences via fold_left *)
Fixpoint allSubseqFold_helper (acc : list (list Z)) (x : Z) : list (list Z) :=
  acc ++ map (fun sub => x :: sub) acc.

Definition allSubseqFold (xs : list Z) : list (list Z) :=
  map (@rev Z) (fold_left allSubseqFold_helper xs [[]]).

(* Filter increasing subsequences and get their lengths *)
Definition increasingSubseqLens (xs : list Z) : list nat :=
  let allSubseq := allSubseqFold xs in
  let increasing := filter isPairwiseLess allSubseq in
  map (@length Z) increasing.

(* Check if a list contains an element *)
Fixpoint contains_nat (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | x :: xs => Nat.eqb x n || contains_nat xs n
  end.

(* Check if all elements satisfy a predicate *)
Fixpoint all_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => f x && all_nat f xs
  end.

Definition longestIncreasingSubseqLength_postcond_dec (xs : list Z) (result : nat) : bool :=
  let lens := increasingSubseqLens xs in
  contains_nat lens result && all_nat (fun n => Nat.leb n result) lens.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubseqLength_postcond (xs : (list Z)) (result : nat) (h_precond : longestIncreasingSubseqLength_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  let allSubseq := allSubseqFold xs in
let increasingSubseqLens := map (@length Z) (filter isPairwiseLess allSubseq) in
In result increasingSubseqLens /\ Forall (fun n => (n <= result)%nat) increasingSubseqLens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubseqLength_postcond_satisfied (xs : (list Z)) (h_precond : longestIncreasingSubseqLength_precond xs) :
    longestIncreasingSubseqLength_postcond xs (longestIncreasingSubseqLength xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
