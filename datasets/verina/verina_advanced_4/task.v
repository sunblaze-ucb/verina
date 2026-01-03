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
Definition LongestIncreasingSubsequence_precond_dec (a : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition LongestIncreasingSubsequence_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition LongestIncreasingSubsequence (a : (list Z)) (h_precond : LongestIncreasingSubsequence_precond a) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LongestIncreasingSubsequence_postcond_dec (a : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition LongestIncreasingSubsequence_postcond (a : (list Z)) (result : Z) (h_precond : LongestIncreasingSubsequence_precond a) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem LongestIncreasingSubsequence_postcond_satisfied (a : (list Z)) (h_precond : LongestIncreasingSubsequence_precond a) :
    LongestIncreasingSubsequence_postcond a (LongestIncreasingSubsequence a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
