(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
Require Import String.
Require Import Ascii.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition sumOfDigits_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sumOfDigits_loop (fuel : nat) (n : nat) (acc : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (n =? 0)%nat then acc
    else sumOfDigits_loop fuel' (n / 10)%nat (acc + n mod 10)%nat
  end.
(* !benchmark @end code_aux *)

Definition sumOfDigits (n : nat) : nat :=
  (* !benchmark @start code *)
  sumOfDigits_loop n n 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nat_to_digits (fuel : nat) (n : nat) : list nat :=
  match fuel with
  | O => [n mod 10]
  | S fuel' =>
    if (n <? 10)%nat then [n]
    else nat_to_digits fuel' (n / 10)%nat ++ [n mod 10]
  end.

Definition sum_of_digit_list (n : nat) : nat :=
  fold_left (fun acc d => (acc + d)%nat) (nat_to_digits n n) 0.
(* !benchmark @end postcond_aux *)

Definition sumOfDigits_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((result - sum_of_digit_list n =? 0)%nat && (sum_of_digit_list n - result =? 0)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfDigits_postcond_satisfied (n : nat) :
    sumOfDigits_precond n = true ->
    sumOfDigits_postcond n (sumOfDigits n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
