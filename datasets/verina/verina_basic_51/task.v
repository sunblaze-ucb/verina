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
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Fixpoint StronglySorted_le (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => (Forall (fun y => (x <= y)%Z) xs) /\ StronglySorted_le xs
  end.

Fixpoint StronglySorted_le_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => (forallb (fun y => (x <=? y)%Z) xs) && (StronglySorted_le_dec xs)
  end.

Definition BinarySearch_precond_dec (a : list Z) (key : Z) : bool :=
  StronglySorted_le_dec a.
(* !benchmark @end precond_aux *)

Definition BinarySearch_precond (a : (list Z)) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  StronglySorted_le a
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint binarySearchLoop (a : list Z) (key : Z) (lo hi : nat) (fuel : nat) : nat :=
  match fuel with
  | O => lo
  | S fuel' =>
      if (lo <? hi)%nat then
        let mid := Nat.div (lo + hi) 2 in
        match nth_error a mid with
        | Some amid =>
            if (amid <? key)%Z then
              binarySearchLoop a key (mid + 1)%nat hi fuel'
            else
              binarySearchLoop a key lo mid fuel'
        | None => lo
        end
      else
        lo
  end.
(* !benchmark @end code_aux *)

Definition BinarySearch (a : (list Z)) (key : Z) (h_precond : BinarySearch_precond a key) : nat :=
  (* !benchmark @start code *)
  binarySearchLoop a key 0%nat (length a) (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Definition all_lt (l : list Z) (key : Z) : Prop :=
  Forall (fun x => (x < key)%Z) l.

Definition all_ge (l : list Z) (key : Z) : Prop :=
  Forall (fun x => (x >= key)%Z) l.

Definition all_lt_dec (l : list Z) (key : Z) : bool :=
  forallb (fun x => (x <? key)%Z) l.

Definition all_ge_dec (l : list Z) (key : Z) : bool :=
  forallb (fun x => (x >=? key)%Z) l.

Definition BinarySearch_postcond_dec (a : list Z) (key : Z) (result : nat) : bool :=
  (result <=? length a)%nat &&
  all_lt_dec (firstn result a) key &&
  all_ge_dec (skipn result a) key.
(* !benchmark @end postcond_aux *)

Definition BinarySearch_postcond (a : (list Z)) (key : Z) (result : nat) (h_precond : BinarySearch_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  (result <= length a)%nat /\
  all_lt (firstn result a) key /\
  all_ge (skipn result a) key
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem BinarySearch_postcond_satisfied (a : (list Z)) (key : Z) (h_precond : BinarySearch_precond a key) :
    BinarySearch_postcond a key (BinarySearch a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
