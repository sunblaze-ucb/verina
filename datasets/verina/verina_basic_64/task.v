(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)

Fixpoint repeat_char (c : ascii) (n : nat) : list ascii :=
  match n with
  | O => []
  | S n' => c :: repeat_char c n'
  end.

Fixpoint list_set (l : list ascii) (i : nat) (c : ascii) : list ascii :=
  match l, i with
  | [], _ => []
  | x :: xs, O => c :: xs
  | x :: xs, S i' => x :: list_set xs i' c
  end.

Fixpoint nth_default (l : list ascii) (n : nat) (default : ascii) : ascii :=
  match l, n with
  | [], _ => default
  | x :: xs, O => x
  | x :: xs, S n' => nth_default xs n' default
  end.

Fixpoint seq (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq (S start) len'
  end.

Fixpoint foldl_range {A : Type} (f : A -> nat -> A) (acc : A) (n : nat) : A :=
  match n with
  | O => acc
  | S n' => f (foldl_range f acc n') n'
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Definition insert_precond_dec (oline : list ascii) (l : nat) (nl : list ascii) (p : nat) (atPos : nat) : bool :=
  andb (andb (Nat.leb l (length oline)) (Nat.leb p (length nl))) (Nat.leb atPos l).
(* !benchmark @end precond_aux *)

Definition insert_precond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) : Prop :=
  (* !benchmark @start precond *)
  (l <= length oline)%nat /\ (p <= length nl)%nat /\ (atPos <= l)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition insert (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (h_precond : insert_precond oline l nl p atPos) : (list ascii) :=
  (* !benchmark @start code *)
  let result := repeat_char " "%char (l + p) in
  let result := foldl_range
    (fun acc i =>
      if Nat.ltb i atPos then list_set acc i (nth_default oline i " "%char) else acc)
    result
    l in
  let result := foldl_range
    (fun acc i =>
      list_set acc (atPos + i) (nth_default nl i " "%char))
    result
    p in
  let result := foldl_range
    (fun acc i =>
      if Nat.leb atPos i then list_set acc (i + p) (nth_default oline i " "%char) else acc)
    result
    l in
  result
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Fixpoint all_range (pred : nat -> bool) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => andb (pred n') (all_range pred n')
  end.

Definition insert_postcond_dec (oline : list ascii) (l : nat) (nl : list ascii) (p : nat) (atPos : nat) (result : list ascii) : bool :=
  andb (andb (andb (Nat.eqb (length result) (l + p))
    (all_range (fun i => Ascii.eqb (nth_default result (atPos + i) " "%char) (nth_default nl i " "%char)) p))
    (all_range (fun i => Ascii.eqb (nth_default result i " "%char) (nth_default oline i " "%char)) atPos))
    (all_range (fun i => Ascii.eqb (nth_default result (atPos + p + i) " "%char) (nth_default oline (atPos + i) " "%char)) (l - atPos)).
(* !benchmark @end postcond_aux *)

Definition insert_postcond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (result : (list ascii)) (h_precond : insert_precond oline l nl p atPos) : Prop :=
  (* !benchmark @start postcond *)
  (length result = l + p)%nat /\
  (forall i, (i < p)%nat -> nth_default result (atPos + i) " "%char = nth_default nl i " "%char) /\
  (forall i, (i < atPos)%nat -> nth_default result i " "%char = nth_default oline i " "%char) /\
  (forall i, (i < l - atPos)%nat -> nth_default result (atPos + p + i) " "%char = nth_default oline (atPos + i) " "%char)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insert_postcond_satisfied (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (h_precond : insert_precond oline l nl p atPos) :
    insert_postcond oline l nl p atPos (insert oline l nl p atPos h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
