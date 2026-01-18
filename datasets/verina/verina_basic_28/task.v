(* !benchmark @start import type=task *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* empty *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isPrime_precond_dec (n : nat) : bool :=
  (2 <=? n)%nat.
(* !benchmark @end precond_aux *)

Definition isPrime_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  (2 <= n)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint check (n i fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if (n <? i * i)%nat then true
      else if (n mod i =? 0)%nat then false
      else check n (i + 1) fuel'
  end.
(* !benchmark @end code_aux *)

Definition isPrime (n : nat) (h_precond : isPrime_precond n) : bool :=
  (* !benchmark @start code *)
  let bound := n in
check n 2 bound
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint seq_from (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq_from (S start) len'
  end.

Definition forallb_custom {A : Type} (f : A -> bool) (l : list A) : bool :=
  forallb f l.

Definition existsb_custom {A : Type} (f : A -> bool) (l : list A) : bool :=
  existsb f l.

Definition isPrime_postcond_dec (n : nat) (result : bool) : bool :=
  let range := seq_from 2 (n - 2) in
  if result then
    forallb_custom (fun k => negb (n mod k =? 0)%nat) range
  else
    existsb_custom (fun k => (n mod k =? 0)%nat) range.
(* !benchmark @end postcond_aux *)

Definition isPrime_postcond (n : nat) (result : bool) (h_precond : isPrime_precond n) : Prop :=
  (* !benchmark @start postcond *)
  let range := seq_from 2 (n - 2) in
(result = true -> Forall (fun k => ~(n mod k = 0)%nat) range) /\
(result = false -> Exists (fun k => (n mod k = 0)%nat) range)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPrime_postcond_satisfied (n : nat) (h_precond : isPrime_precond n) :
    isPrime_postcond n (isPrime n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
