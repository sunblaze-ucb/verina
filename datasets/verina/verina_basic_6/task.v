(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition minOfThree_precond (a : Z) (b : Z) (c : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition minOfThree (a : Z) (b : Z) (c : Z) : Z :=
  (* !benchmark @start code *)
  if (a <=? b) && (a <=? c) then a
  else if (b <=? a) && (b <=? c) then b
  else c
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition minOfThree_postcond (a : Z) (b : Z) (c : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  ((result <=? a) && (result <=? b) && (result <=? c)) &&
  ((result =? a) || (result =? b) || (result =? c))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minOfThree_postcond_satisfied (a : Z) (b : Z) (c : Z) :
    minOfThree_precond a b c = true ->
    minOfThree_postcond a b c (minOfThree a b c) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
