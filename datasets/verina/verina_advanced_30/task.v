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
Definition longestIncreasingStreak_precond_dec (nums : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingStreak_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition longestIncreasingStreak (nums : (list Z)) (h_precond : longestIncreasingStreak_precond nums) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestIncreasingStreak_postcond_dec (nums : (list Z)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingStreak_postcond (nums : (list Z)) (result : nat) (h_precond : longestIncreasingStreak_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem longestIncreasingStreak_postcond_satisfied (nums : (list Z)) (h_precond : longestIncreasingStreak_precond nums) :
    longestIncreasingStreak_postcond nums (longestIncreasingStreak nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
