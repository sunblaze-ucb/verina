(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition longestIncreasingSubseqLength_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Generate all subsequences *)
Fixpoint subsequences {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let subs := subsequences xs' in
    subs ++ map (fun s => x :: s) subs
  end.

(* Check if a list is strictly increasing *)
Fixpoint isStrictlyIncreasing (xs : list Z) : bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: ((y :: rest) as tail) => if (x <? y)%Z then isStrictlyIncreasing tail else false
  end.

(* Fold to find maximum length *)
Definition maxLength (subs : list (list Z)) : nat :=
  fold_left (fun acc s => Nat.max acc (length s)) subs 0%nat.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubseqLength (xs : (list Z)) : nat :=
  (* !benchmark @start code *)
  let subs := subsequences xs in
  let increasing := filter isStrictlyIncreasing subs in
  maxLength increasing
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Generate all subsequences by folding *)
Definition allSubseqFold (xs : list Z) : list (list Z) :=
  map (@rev Z) (fold_left (fun acc x => acc ++ map (fun sub => x :: sub) acc) xs [[]]).

(* Check if a list is pairwise strictly increasing *)
Fixpoint pairwiseLt (xs : list Z) : bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tail) => (x <? y)%Z && pairwiseLt tail
  end.

(* Check if result is in a list of nats *)
Fixpoint nat_in_list (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => (n =? h)%nat || nat_in_list n t
  end.

(* Check if all elements in list are <= n *)
Fixpoint all_le_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => true
  | h :: t => (h <=? n)%nat && all_le_nat n t
  end.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubseqLength_postcond (xs : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let allSubseq := allSubseqFold xs in
  let increasingSubseqs := filter pairwiseLt allSubseq in
  let increasingSubseqLens := map (@length Z) increasingSubseqs in
  nat_in_list result increasingSubseqLens && all_le_nat result increasingSubseqLens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubseqLength_postcond_satisfied (xs : (list Z)) :
    longestIncreasingSubseqLength_precond xs = true ->
    longestIncreasingSubseqLength_postcond xs (longestIncreasingSubseqLength xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
