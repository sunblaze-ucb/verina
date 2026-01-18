(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)

Fixpoint eraseIdx {A : Type} (l : list A) (i : nat) : list A :=
  match l, i with
  | [], _ => []
  | _ :: tl, 0 => tl
  | hd :: tl, S i' => hd :: eraseIdx tl i'
  end.

Fixpoint split (l : list (nat * nat)) : (list (nat * nat) * list (nat * nat)) :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      let (l1, l2) := split rest in
      (x :: l1, y :: l2)
  end.

Fixpoint merge (l1 l2 : list (nat * nat)) : list (nat * nat) :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | (a1, b1) :: t1, (a2, b2) :: t2 =>
      if (a1 <=? a2)%nat then (a1, b1) :: merge t1 l2
      else (a2, b2) :: merge l1 t2
  end.

Fixpoint mergeSort (l : list (nat * nat)) (n : nat) : list (nat * nat) :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | [x] => [x]
      | _ =>
          let (l1, l2) := split l in
          merge (mergeSort l1 n') (mergeSort l2 n')
      end
  end.

Definition mergeInterval (acc : list (nat * nat)) (curr : nat * nat) : list (nat * nat) :=
  match acc with
  | [] => [curr]
  | (s, e) :: rest =>
      if (fst curr <=? e)%nat then (s, Nat.max e (snd curr)) :: rest
      else curr :: acc
  end.

Definition computeCoverage (intervals : list (nat * nat)) (i : nat) : nat :=
  let remaining := eraseIdx intervals i in
  let sorted := mergeSort remaining (length remaining) in
  let merged := fold_left mergeInterval sorted [] in
  let coverage := fold_left (fun acc p => (acc + (snd p - fst p))%nat) (rev merged) 0%nat in
  coverage.

Fixpoint maxInRangeAux (intervals : list (nat * nat)) (i : nat) (fuel : nat) (acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
      if (i <? length intervals)%nat then
        let cov := computeCoverage intervals i in
        maxInRangeAux intervals (S i) fuel' (Nat.max acc cov)
      else acc
  end.

Definition maxInRange (intervals : list (nat * nat)) : nat :=
  maxInRangeAux intervals 0%nat (length intervals) 0%nat.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Definition maxCoverageAfterRemovingOne_precond_dec (intervals : list (nat * nat)) : bool :=
  (length intervals >? 0)%nat.
(* !benchmark @end precond_aux *)

Definition maxCoverageAfterRemovingOne_precond (intervals : (list (nat * nat))) : Prop :=
  (* !benchmark @start precond *)
  (length intervals > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition maxCoverageAfterRemovingOne (intervals : (list (nat * nat))) (h_precond : maxCoverageAfterRemovingOne_precond intervals) : nat :=
  (* !benchmark @start code *)
  let n := length intervals in
  if n <=? 1 then 0%nat
  else maxInRange intervals
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Definition maxCoverageAfterRemovingOne_postcond_dec (intervals : list (nat * nat)) (result : nat) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition maxCoverageAfterRemovingOne_postcond (intervals : (list (nat * nat))) (result : nat) (h_precond : maxCoverageAfterRemovingOne_precond intervals) : Prop :=
  (* !benchmark @start postcond *)
  exists i : nat, (i < length intervals)%nat /\
  let remaining := eraseIdx intervals i in
  let sorted := mergeSort remaining (length remaining) in
  let merged := fold_left mergeInterval sorted [] in
  let cov := fold_left (fun acc p => (acc + (snd p - fst p))%nat) (rev merged) 0%nat in
  result = cov /\
  forall j : nat, (j < length intervals)%nat ->
    let rem_j := eraseIdx intervals j in
    let sort_j := mergeSort rem_j (length rem_j) in
    let merged_j := fold_left mergeInterval sort_j [] in
    let cov_j := fold_left (fun acc p => (acc + (snd p - fst p))%nat) (rev merged_j) 0%nat in
    (cov >= cov_j)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxCoverageAfterRemovingOne_postcond_satisfied (intervals : (list (nat * nat))) (h_precond : maxCoverageAfterRemovingOne_precond intervals) :
    maxCoverageAfterRemovingOne_postcond intervals (maxCoverageAfterRemovingOne intervals h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
