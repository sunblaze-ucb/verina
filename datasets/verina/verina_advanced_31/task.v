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
Definition longestIncreasingSubseqLength_precond_dec (xs : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubseqLength_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition longestIncreasingSubseqLength (xs : (list Z)) (h_precond : longestIncreasingSubseqLength_precond xs) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestIncreasingSubseqLength_postcond_dec (xs : (list Z)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubseqLength_postcond (xs : (list Z)) (result : nat) (h_precond : longestIncreasingSubseqLength_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubseqLength_postcond_satisfied (xs : (list Z)) (h_precond : longestIncreasingSubseqLength_precond xs) :
    longestIncreasingSubseqLength_postcond xs (longestIncreasingSubseqLength xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
