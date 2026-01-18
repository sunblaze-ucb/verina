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
Definition longestIncreasingSubsequence_precond_dec (nums : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition max2 (a b : nat) : nat :=
  if (a >? b)%nat then a else b.

Fixpoint helper (lst : list Z) (prev : option Z) : nat :=
  match lst with
  | [] => 0%nat
  | h :: t =>
      let canTake : bool :=
        match prev with
        | None => true
        | Some p => (p <? h)%Z
        end in
      let withTake : nat :=
        if canTake then (1 + helper t (Some h))%nat else 0%nat in
      let withoutTake : nat := helper t prev in
      max2 withTake withoutTake
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (nums : (list Z)) (h_precond : longestIncreasingSubsequence_precond nums) : nat :=
  (* !benchmark @start code *)
  helper nums None
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allSubseq_helper (nums : list Z) : list (list Z) :=
  match nums with
  | [] => [[]]
  | x :: xs =>
      let acc := allSubseq_helper xs in
      acc ++ (map (fun sub => x :: sub) acc)
  end.

Definition allSubseq (nums : list Z) : list (list Z) :=
  map (@rev Z) (allSubseq_helper nums).

Fixpoint pairwise_lt (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: rest) as tail =>
      if (x <? y)%Z then pairwise_lt tail else false
  end.

Definition increasingSubseqLens (nums : list Z) : list nat :=
  let allSeqs := allSubseq nums in
  let increasing := filter pairwise_lt allSeqs in
  map (@length Z) increasing.

Fixpoint contains_nat (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | x :: xs => if (Nat.eqb x n) then true else contains_nat xs n
  end.

Fixpoint all_leq (l : list nat) (n : nat) : bool :=
  match l with
  | [] => true
  | x :: xs => if (x <=? n)%nat then all_leq xs n else false
  end.

Definition longestIncreasingSubsequence_postcond_dec (nums : list Z) (result : nat) : bool :=
  let lens := increasingSubseqLens nums in
  andb (contains_nat lens result) (all_leq lens result).
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (nums : (list Z)) (result : nat) (h_precond : longestIncreasingSubsequence_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let allSeqs := allSubseq nums in
let increasing := filter pairwise_lt allSeqs in
let lens := map (@length Z) increasing in
(exists i, nth_error lens i = Some result) /\ (forall len, In len lens -> (len <= result)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (nums : (list Z)) (h_precond : longestIncreasingSubsequence_precond nums) :
    longestIncreasingSubsequence_postcond nums (longestIncreasingSubsequence nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
