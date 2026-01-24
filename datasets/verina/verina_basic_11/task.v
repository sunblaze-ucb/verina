(* !benchmark @start import type=task *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition lastDigit_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition lastDigit (n : nat) : nat :=
  (* !benchmark @start code *)
  n mod 10
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition lastDigit_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((0 <=? result)%nat && (result <? 10)%nat) && ((n mod 10 - result =? 0)%nat && (result - n mod 10 =? 0)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lastDigit_postcond_satisfied (n : nat) :
    lastDigit_precond n = true ->
    lastDigit_postcond n (lastDigit n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
