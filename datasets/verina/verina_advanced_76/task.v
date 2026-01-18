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

Fixpoint removeDups (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if existsb (Z.eqb x) xs then removeDups xs else x :: removeDups xs
  end.

Definition topKFrequent_precond_dec (nums : list Z) (k : nat) : bool :=
  (k <=? length (removeDups nums))%nat.
(* !benchmark @end precond_aux *)

Definition topKFrequent_precond (nums : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  (k <= length (removeDups nums))%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint find_freq (n : Z) (freqList : list (Z * nat)) : option (Z * nat) :=
  match freqList with
  | [] => None
  | (key, cnt) :: rest =>
      if Z.eqb key n then Some (key, cnt) else find_freq n rest
  end.

Fixpoint update_freq (n : Z) (freqList : list (Z * nat)) : list (Z * nat) :=
  match freqList with
  | [] => []
  | (key, cnt) :: rest =>
      if Z.eqb key n then (key, S cnt) :: rest else (key, cnt) :: update_freq n rest
  end.

Fixpoint build_freqList (nums : list Z) : list (Z * nat) :=
  fold_left (fun acc n =>
    match find_freq n acc with
    | Some _ => update_freq n acc
    | None => acc ++ [(n, 1%nat)]
    end) nums [].

Fixpoint insertSorted (pair : Z * nat) (xs : list (Z * nat)) : list (Z * nat) :=
  let (x, cx) := pair in
  match xs with
  | [] => [pair]
  | (y, cy) :: ys =>
      if (cy <? cx)%nat then
        pair :: (y, cy) :: ys
      else
        (y, cy) :: insertSorted pair ys
  end.

Definition sort_by_freq (freqList : list (Z * nat)) : list (Z * nat) :=
  fold_left (fun acc pair => insertSorted pair acc) freqList []
(* !benchmark @end code_aux *)

Definition topKFrequent (nums : (list Z)) (k : nat) (h_precond : topKFrequent_precond nums k) : (list Z) :=
  (* !benchmark @start code *)
  let freqList := build_freqList nums in
  let sorted := sort_by_freq freqList in
  map fst (firstn k sorted)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Fixpoint count_occurrences (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Z.eqb x y then S (count_occurrences x ys) else count_occurrences x ys
  end.

Fixpoint all_in (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => true
  | x :: xs => existsb (Z.eqb x) l2 && all_in xs l2
  end.

Fixpoint pairwise_distinct (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (Z.eqb x) xs) && pairwise_distinct xs
  end.

Fixpoint all_freq_check (result nums : list Z) : bool :=
  forallb (fun x =>
    forallb (fun y =>
      existsb (Z.eqb y) result || (count_occurrences x nums >=? count_occurrences y nums)%nat
    ) nums
  ) result.

Fixpoint pairwise_freq_ordered (result nums : list Z) (idx : nat) : bool :=
  match result with
  | [] => true
  | x :: xs =>
      forallb (fun y =>
        (count_occurrences x nums >=? count_occurrences y nums)%nat
      ) xs && pairwise_freq_ordered xs nums (S idx)
  end.

Definition topKFrequent_postcond_dec (nums : list Z) (k : nat) (result : list Z) : bool :=
  (length result =? k)%nat &&
  all_in result nums &&
  pairwise_distinct result &&
  all_freq_check result nums &&
  pairwise_freq_ordered result nums 0%nat.
(* !benchmark @end postcond_aux *)

Definition topKFrequent_postcond (nums : (list Z)) (k : nat) (result : (list Z)) (h_precond : topKFrequent_precond nums k) : Prop :=
  (* !benchmark @start postcond *)
  length result = k /\
  (forall x, In x result -> In x nums) /\
  NoDup result /\
  (forall x, In x result ->
    forall y, In y nums ->
      In y result \/ (count_occurrences x nums >= count_occurrences y nums)%nat) /\
  (forall i j x y,
    nth_error result i = Some x ->
    nth_error result j = Some y ->
    (i < j)%nat ->
    (count_occurrences x nums >= count_occurrences y nums)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem topKFrequent_postcond_satisfied (nums : (list Z)) (k : nat) (h_precond : topKFrequent_precond nums k) :
    topKFrequent_postcond nums k (topKFrequent nums k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
