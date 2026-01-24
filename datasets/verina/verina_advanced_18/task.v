(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Ascii.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition isArmstrong_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countDigits_go (fuel : nat) (n acc : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (n =? 0)%nat then acc
    else countDigits_go fuel' (n / 10)%nat (acc + 1)%nat
  end.

Definition countDigits (n : nat) : nat :=
  countDigits_go (n + 1)%nat n (if (n =? 0)%nat then 1%nat else 0%nat).

Fixpoint sumPowers_go (fuel : nat) (n acc k : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (n =? 0)%nat then acc
    else
      let digit := (n mod 10)%nat in
      sumPowers_go fuel' (n / 10)%nat (acc + Nat.pow digit k)%nat k
  end.

Definition sumPowers (n k : nat) : nat :=
  sumPowers_go (n + 1)%nat n 0%nat k.
(* !benchmark @end code_aux *)

Definition isArmstrong (n : nat) : bool :=
  (* !benchmark @start code *)
  let k := countDigits n in
  (sumPowers n k =? n)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nat_to_digits_aux (fuel : nat) (n : nat) (acc : list nat) : list nat :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (n =? 0)%nat then acc
    else nat_to_digits_aux fuel' (n / 10)%nat ((n mod 10)%nat :: acc)
  end.

Definition nat_to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then [0%nat]
  else nat_to_digits_aux (n + 1)%nat n [].

Definition postcond_countDigits (n : nat) : nat :=
  List.length (nat_to_digits n).

Definition postcond_sum (n : nat) : nat :=
  let digits := nat_to_digits n in
  let k := postcond_countDigits n in
  fold_left (fun acc d => (acc + Nat.pow d k)%nat) digits 0%nat.
(* !benchmark @end postcond_aux *)

Definition isArmstrong_postcond (n : nat) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let n' := postcond_sum n in
  implb result (n =? n')%nat && implb (negb result) (negb (n =? n')%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isArmstrong_postcond_satisfied (n : nat) :
    isArmstrong_precond n = true ->
    isArmstrong_postcond n (isArmstrong n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
