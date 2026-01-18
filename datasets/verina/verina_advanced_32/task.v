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
Require Import Coq.Arith.Arith.
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
Definition longestIncreasingSubsequence_precond_dec (numbers : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (numbers : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to find the maximum length in a list of natural numbers *)
Fixpoint findMaxLength (lengths : list nat) : nat :=
  match lengths with
  | [] => 0%nat
  | x :: xs =>
      let maxRest := findMaxLength xs in
      if Nat.ltb maxRest x then x else maxRest
  end.

(* Helper function to find the best length ending at the current element *)
Fixpoint findLengthEndingAtCurr (prevVals : list Z) (prevLens : list nat) (currNum : Z) (best : nat) : nat :=
  match prevVals, prevLens with
  | [], _ => best
  | _, [] => best
  | prevVal :: restVals, prevLen :: restLens =>
      if (prevVal <? currNum)%Z then
        findLengthEndingAtCurr restVals restLens currNum (Nat.max best prevLen)
      else
        findLengthEndingAtCurr restVals restLens currNum best
  end.

(* Main recursive function to build tables *)
Fixpoint buildTables (nums : list Z) (prevNums : list Z) (lengths : list nat) (idx : nat) : nat :=
  match nums with
  | [] => findMaxLength lengths
  | currNum :: restNums =>
      let bestPrevLen := findLengthEndingAtCurr prevNums lengths currNum 0%nat in
      let currLength := (bestPrevLen + 1)%nat in
      buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (numbers : (list Z)) (h_precond : longestIncreasingSubsequence_precond numbers) : nat :=
  (* !benchmark @start code *)
  match numbers with
| [] => 0%nat
| [x] => 1%nat
| first :: rest => buildTables rest [first] [1%nat] 1%nat
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to compute all subsequences *)
Fixpoint foldl_app_subseqs (acc : list (list Z)) (nums : list Z) : list (list Z) :=
  match nums with
  | [] => acc
  | x :: xs =>
      let new_acc := acc ++ map (fun sub => x :: sub) acc in
      foldl_app_subseqs new_acc xs
  end.

(* Check if a list is strictly increasing (pairwise <) *)
Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: rest) as tl =>
      if (x <? y)%Z then is_strictly_increasing tl else false
  end.

(* Check if a list contains an element *)
Fixpoint contains_nat (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | x :: xs => if Nat.eqb x n then true else contains_nat xs n
  end.

(* Check if all elements in a list satisfy a predicate *)
Fixpoint all_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => if f x then all_nat f xs else false
  end.

Definition longestIncreasingSubsequence_postcond_dec (numbers : list Z) (result : nat) : bool :=
  let allSubseq := map (@rev Z) (foldl_app_subseqs [[]] numbers) in
  let increasingSubseqs := filter is_strictly_increasing allSubseq in
  let increasingSubseqLens := map (@length Z) increasingSubseqs in
  andb (contains_nat increasingSubseqLens result)
       (all_nat (fun len => (len <=? result)%nat) increasingSubseqLens).
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (numbers : (list Z)) (result : nat) (h_precond : longestIncreasingSubsequence_precond numbers) : Prop :=
  (* !benchmark @start postcond *)
  let allSubseq := map (@rev Z) (foldl_app_subseqs [[]] numbers) in
let increasingSubseqs := filter is_strictly_increasing allSubseq in
let increasingSubseqLens := map (@length Z) increasingSubseqs in
In result increasingSubseqLens /\ Forall (fun len => (len <= result)%nat) increasingSubseqLens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (numbers : (list Z)) (h_precond : longestIncreasingSubsequence_precond numbers) :
    longestIncreasingSubsequence_postcond numbers (longestIncreasingSubsequence numbers h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
