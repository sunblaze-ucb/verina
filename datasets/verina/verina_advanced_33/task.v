(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition max2 (a b : nat) : nat :=
  if (b <? a)%nat then a else b.

Fixpoint helper (lst : list Z) (prev : option Z) : nat :=
  match lst with
  | [] => O
  | h :: t =>
      let canTake : bool :=
        match prev with
        | None => true
        | Some p => (p <? h)%Z
        end in
      let withTake : nat :=
        if canTake then S (helper t (Some h)) else O in
      let withoutTake : nat := helper t prev in
      max2 withTake withoutTake
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (nums : (list Z)) : nat :=
  (* !benchmark @start code *)
  helper nums None
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allSubseqHelper (nums : list Z) (acc : list (list Z)) : list (list Z) :=
  match nums with
  | [] => acc
  | x :: xs => allSubseqHelper xs (acc ++ map (fun sub => x :: sub) acc)
  end.

Definition allSubseq (nums : list Z) : list (list Z) :=
  map (@rev Z) (allSubseqHelper nums [[]]).

Fixpoint isStrictlyIncreasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <? y)%Z && isStrictlyIncreasing rest
  end.

Definition increasingSubseqLens (nums : list Z) : list nat :=
  map (@length Z) (filter isStrictlyIncreasing (allSubseq nums)).

Fixpoint list_nat_contains (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? n)%nat then true else list_nat_contains t n
  end.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (nums : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let lens := increasingSubseqLens nums in
  list_nat_contains lens result && forallb (fun x => (x <=? result)%nat) lens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (nums : (list Z)) :
    longestIncreasingSubsequence_precond nums = true ->
    longestIncreasingSubsequence_postcond nums (longestIncreasingSubsequence nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
