(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (numbers : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findMaxLength (lengths : list nat) : nat :=
  match lengths with
  | [] => O
  | x :: xs =>
      let maxRest := findMaxLength xs in
      if (maxRest <? x)%nat then x else maxRest
  end.

Fixpoint findLengthEndingAtCurr (prevNums : list Z) (prevLens : list nat) (currNum : Z) (best : nat) : nat :=
  match prevNums, prevLens with
  | [], _ => best
  | _, [] => best
  | prevVal :: restVals, prevLen :: restLens =>
      if (prevVal <? currNum)%Z then
        findLengthEndingAtCurr restVals restLens currNum (max best prevLen)
      else
        findLengthEndingAtCurr restVals restLens currNum best
  end.

Fixpoint buildTables (restNums : list Z) (prevNums : list Z) (lengths : list nat) (idx : nat) : nat :=
  match restNums with
  | [] => findMaxLength lengths
  | currNum :: rest =>
      let bestPrevLen := findLengthEndingAtCurr prevNums lengths currNum O in
      let currLength := (bestPrevLen + 1)%nat in
      buildTables rest (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (numbers : (list Z)) : nat :=
  (* !benchmark @start code *)
  match numbers with
  | [] => O
  | [x] => 1%nat
  | first :: rest => buildTables rest [first] [1%nat] 1%nat
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allSubsequences (nums : list Z) : list (list Z) :=
  match nums with
  | [] => [[]]
  | x :: xs =>
      let subs := allSubsequences xs in
      subs ++ map (fun sub => x :: sub) subs
  end.

Fixpoint isStrictlyIncreasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <? y)%Z && isStrictlyIncreasing rest
  end.

Definition getIncreasingSubsequences (nums : list Z) : list (list Z) :=
  filter isStrictlyIncreasing (allSubsequences nums).

Definition getIncreasingSubseqLengths (nums : list Z) : list nat :=
  map (@length Z) (getIncreasingSubsequences nums).

Fixpoint list_nat_contains (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | x :: xs => (x =? n)%nat || list_nat_contains xs n
  end.

Definition allLeq (l : list nat) (n : nat) : bool :=
  forallb (fun x => (x <=? n)%nat) l.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (numbers : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let allSubseqLens := getIncreasingSubseqLengths numbers in
  list_nat_contains allSubseqLens result && allLeq allSubseqLens result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (numbers : (list Z)) :
    longestIncreasingSubsequence_precond numbers = true ->
    longestIncreasingSubsequence_postcond numbers (longestIncreasingSubsequence numbers) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
