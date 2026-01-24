(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
Require Import Bool.
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

Definition binaryToDecimal_precond (digits : (list nat)) : bool :=
  (* !benchmark @start precond *)
  forallb (fun d => (d =? 0)%nat || (d =? 1)%nat) digits
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint binaryToDecimal_helper (digits : list nat) : nat :=
  match digits with
  | [] => 0
  | first :: rest => (first * Nat.pow 2 (length rest) + binaryToDecimal_helper rest)%nat
  end.
(* !benchmark @end code_aux *)

Definition binaryToDecimal (digits : (list nat)) : nat :=
  (* !benchmark @start code *)
  binaryToDecimal_helper digits
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition foldl_binary (digits : list nat) : nat :=
  fold_left (fun acc bit => (acc * 2 + bit)%nat) digits 0.
(* !benchmark @end postcond_aux *)

Definition binaryToDecimal_postcond (digits : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((result - foldl_binary digits =? 0)%nat && (foldl_binary digits - result =? 0)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem binaryToDecimal_postcond_satisfied (digits : (list nat)) :
    binaryToDecimal_precond digits = true ->
    binaryToDecimal_postcond digits (binaryToDecimal digits) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
