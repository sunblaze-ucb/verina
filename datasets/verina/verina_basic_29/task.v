(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition removeElement_precond (s : (list Z)) (k : nat) : bool :=
  (* !benchmark @start precond *)
  (k <? length s)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint removeElement_aux (s : list Z) (k : nat) : list Z :=
  match s with
  | [] => []
  | h :: t =>
    match k with
    | O => t
    | S k' => h :: removeElement_aux t k'
    end
  end.
(* !benchmark @end code_aux *)

Definition removeElement (s : (list Z)) (k : nat) : (list Z) :=
  (* !benchmark @start code *)
  removeElement_aux s k
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_or_zero (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
    match n with
    | O => h
    | S n' => nth_or_zero t n'
    end
  end.

Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_lt n' f
  end.
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (s : (list Z)) (k : nat) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length s - 1)%nat) &&
  forall_nat_lt k (fun i => (nth_or_zero result i =? nth_or_zero s i)) &&
  forall_nat_lt (length result) (fun i => implb (k <=? i)%nat (nth_or_zero result i =? nth_or_zero s (i + 1)%nat))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (s : (list Z)) (k : nat) :
    removeElement_precond s k = true ->
    removeElement_postcond s k (removeElement s k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
