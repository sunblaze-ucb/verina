(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
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
Definition moveZeroes_precond_dec (xs : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition moveZeroes_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition moveZeroes (xs : (list Z)) (h_precond : moveZeroes_precond xs) : (list Z) :=
  (* !benchmark @start code *)
  let nonzeros := filter (fun x => if (x =? 0)%Z then false else true) xs in
let zeros := filter (fun x => if (x =? 0)%Z then true else false) xs in
nonzeros ++ zeros
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

(* Count how many times a specific value appears in the list *)
Fixpoint countVal (val : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs =>
    let rest := countVal val xs in
    if (x =? val)%Z then (rest + 1)%nat else rest
  end.

(* Check whether one list is a subsequence of another (preserving relative order) *)
Fixpoint isSubsequence (xs ys : list Z) : bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if (x =? y)%Z then isSubsequence xt yt else isSubsequence xs yt
  end.

(* Helper to drop elements while predicate holds *)
Fixpoint dropWhile (f : Z -> bool) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if f x then dropWhile f xs else x :: xs
  end.

(* Helper to check all elements satisfy a predicate *)
Fixpoint all (f : Z -> bool) (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => if f x then all f xs else false
  end.

Definition moveZeroes_postcond_dec (xs result : list Z) : bool :=
  let nonzero_filter := filter (fun x => if (x =? 0)%Z then false else true) xs in
  let dropped := dropWhile (fun x => if (x =? 0)%Z then false else true) result in
  andb (andb (andb (isSubsequence nonzero_filter result)
                    (all (fun x => (x =? 0)%Z) dropped))
             (Nat.eqb (countVal 0 xs) (countVal 0 result)))
       (Nat.eqb (length xs) (length result)).
(* !benchmark @end postcond_aux *)

Definition moveZeroes_postcond (xs : (list Z)) (result : (list Z)) (h_precond : moveZeroes_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  isSubsequence (filter (fun x => if (x =? 0)%Z then false else true) xs) result = true /\
all (fun x => (x =? 0)%Z) (dropWhile (fun x => if (x =? 0)%Z then false else true) result) = true /\
countVal 0 xs = countVal 0 result /\
length xs = length result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem moveZeroes_postcond_satisfied (xs : (list Z)) (h_precond : moveZeroes_precond xs) :
    moveZeroes_postcond xs (moveZeroes xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
