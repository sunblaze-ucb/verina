(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint merge_intervals_aux (sorted : list (nat * nat)) (acc : list (nat * nat)) : list (nat * nat) :=
  match sorted with
  | [] => acc
  | curr :: rest =>
    match acc with
    | [] => merge_intervals_aux rest [curr]
    | (s, e) :: acc_rest =>
      if (fst curr <=? e)%nat then
        merge_intervals_aux rest ((s, max e (snd curr)) :: acc_rest)
      else
        merge_intervals_aux rest (curr :: acc)
    end
  end.

Fixpoint compute_coverage (merged : list (nat * nat)) : nat :=
  match merged with
  | [] => O
  | (s, e) :: rest => ((e - s) + compute_coverage rest)%nat
  end.

Fixpoint eraseIdx {A : Type} (l : list A) (i : nat) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => t
  | h :: t, S i' => h :: eraseIdx t i'
  end.

Fixpoint insert_sorted (x : nat * nat) (l : list (nat * nat)) : list (nat * nat) :=
  match l with
  | [] => [x]
  | h :: t =>
    if (fst x <=? fst h)%nat then x :: h :: t
    else h :: insert_sorted x t
  end.

Fixpoint sort_intervals (l : list (nat * nat)) : list (nat * nat) :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_intervals t)
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition maxCoverageAfterRemovingOne_precond (intervals : (list (nat * nat))) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length intervals)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition coverage_after_remove (intervals : list (nat * nat)) (i : nat) : nat :=
  let remaining := eraseIdx intervals i in
  let sorted := sort_intervals remaining in
  let merged := merge_intervals_aux sorted [] in
  compute_coverage (rev merged).

Fixpoint max_coverage_loop (intervals : list (nat * nat)) (i : nat) (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S n' =>
    let cov := coverage_after_remove intervals i in
    max_coverage_loop intervals (S i) n' (max acc cov)
  end.
(* !benchmark @end code_aux *)

Definition maxCoverageAfterRemovingOne (intervals : (list (nat * nat))) : nat :=
  (* !benchmark @start code *)
  let n := length intervals in
    if (n <=? 1)%nat then O
    else max_coverage_loop intervals O n O
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint existsb_indexed {A : Type} (f : nat -> A -> bool) (l : list A) (start : nat) : bool :=
  match l with
  | [] => false
  | h :: t => f start h || existsb_indexed f t (S start)
  end.

Fixpoint forallb_indexed {A : Type} (f : nat -> A -> bool) (l : list A) (start : nat) : bool :=
  match l with
  | [] => true
  | h :: t => f start h && forallb_indexed f t (S start)
  end.

Definition coverage_for_index (intervals : list (nat * nat)) (i : nat) : nat :=
  let remaining := eraseIdx intervals i in
  let sorted := sort_intervals remaining in
  let merged := merge_intervals_aux sorted [] in
  compute_coverage (rev merged).
(* !benchmark @end postcond_aux *)

Definition maxCoverageAfterRemovingOne_postcond (intervals : (list (nat * nat))) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  existsb_indexed (fun i _ =>
    let cov := coverage_for_index intervals i in
    (result =? cov)%nat &&
    forallb_indexed (fun j _ =>
      let cov_j := coverage_for_index intervals j in
      (cov_j <=? cov)%nat
    ) intervals O
  ) intervals O
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxCoverageAfterRemovingOne_postcond_satisfied (intervals : (list (nat * nat))) :
    maxCoverageAfterRemovingOne_precond intervals = true ->
    maxCoverageAfterRemovingOne_postcond intervals (maxCoverageAfterRemovingOne intervals) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
