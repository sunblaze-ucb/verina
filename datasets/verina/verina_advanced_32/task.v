(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition longestIncreasingSubsequence_precond_dec (numbers : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (numbers : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (numbers : (list Z)) (h_precond : longestIncreasingSubsequence_precond numbers) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestIncreasingSubsequence_postcond_dec (numbers : (list Z)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (numbers : (list Z)) (result : nat) (h_precond : longestIncreasingSubsequence_precond numbers) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (numbers : (list Z)) (h_precond : longestIncreasingSubsequence_precond numbers) :
    longestIncreasingSubsequence_postcond numbers (longestIncreasingSubsequence numbers h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
