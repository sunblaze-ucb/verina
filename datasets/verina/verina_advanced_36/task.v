(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint count_occurrences (target : nat) (lst : list nat) : nat :=
  match lst with
  | [] => 0%nat
  | y :: ys =>
    if Nat.eqb y target then S (count_occurrences target ys)
    else count_occurrences target ys
  end.

Fixpoint existsb_count (xs : list nat) (threshold : nat) : bool :=
  match xs with
  | [] => false
  | y :: ys =>
    if Nat.ltb threshold (count_occurrences y xs) then true
    else existsb_count ys threshold
  end.

Definition majorityElement_precond_dec (xs : list nat) : bool :=
  andb (Nat.ltb 0%nat (length xs)) (existsb_count xs (Nat.div (length xs) 2%nat)).
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (xs : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  (length xs > 0)%nat /\ exists x, In x xs /\ count_occurrences x xs > (length xs) / 2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findCandidate (lst : list nat) (candidate : option nat) (count : nat) : nat :=
  match lst with
  | [] =>
    match candidate with
    | Some c => c
    | None => 0%nat
    end
  | x :: xs =>
    match candidate with
    | Some c =>
      if Nat.eqb x c then
        findCandidate xs (Some c) (count + 1)%nat
      else if Nat.eqb count 0%nat then
        findCandidate xs (Some x) 1%nat
      else
        findCandidate xs (Some c) (count - 1)%nat
    | None =>
      findCandidate xs (Some x) 1%nat
    end
  end.
(* !benchmark @end code_aux *)

Definition majorityElement (xs : (list nat)) (h_precond : majorityElement_precond xs) : nat :=
  (* !benchmark @start code *)
  let cand := findCandidate xs None 0%nat in cand
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition majorityElement_postcond_dec (xs : list nat) (result : nat) : bool :=
  let count := count_occurrences result xs in
  Nat.ltb (Nat.div (length xs) 2%nat) count.
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (xs : (list nat)) (result : nat) (h_precond : majorityElement_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  let count := count_occurrences result xs in
count > (length xs) / 2
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (xs : (list nat)) (h_precond : majorityElement_precond xs) :
    majorityElement_postcond xs (majorityElement xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
