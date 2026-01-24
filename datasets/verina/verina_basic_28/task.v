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

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition isPrime_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  (2 <=? n)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint check (n i fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if (n <? i * i)%nat then true
    else if (n mod i =? 0)%nat then false
    else check n (i + 1)%nat fuel'
  end.
(* !benchmark @end code_aux *)

Definition isPrime (n : nat) : bool :=
  (* !benchmark @start code *)
  check n 2 n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range' (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: range' (S start) len'
  end.

Definition all_not_divisible (n : nat) (l : list nat) : bool :=
  forallb (fun k => negb (n mod k =? 0)%nat) l.

Definition any_divisible (n : nat) (l : list nat) : bool :=
  existsb (fun k => (n mod k =? 0)%nat) l.
(* !benchmark @end postcond_aux *)

Definition isPrime_postcond (n : nat) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  implb result (all_not_divisible n (range' 2 (n - 2))) &&
  implb (negb result) (any_divisible n (range' 2 (n - 2)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPrime_postcond_satisfied (n : nat) :
    isPrime_precond n = true ->
    isPrime_postcond n (isPrime n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
