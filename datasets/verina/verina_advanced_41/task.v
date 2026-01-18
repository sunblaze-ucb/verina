(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* empty *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxOfThree_precond_dec (a : Z) (b : Z) (c : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition maxOfThree_precond (a : Z) (b : Z) (c : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Require Import Bool.
(* !benchmark @end code_aux *)

Definition maxOfThree (a : Z) (b : Z) (c : Z) (h_precond : maxOfThree_precond a b c) : Z :=
  (* !benchmark @start code *)
  if andb (a >=? b) (a >=? c) then a
else if andb (b >=? a) (b >=? c) then b
else c
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Bool.

Definition maxOfThree_postcond_dec (a : Z) (b : Z) (c : Z) (result : Z) : bool :=
  andb (andb (andb (result >=? a) (result >=? b)) (result >=? c))
       (orb (orb (result =? a) (result =? b)) (result =? c)).
(* !benchmark @end postcond_aux *)

Definition maxOfThree_postcond (a : Z) (b : Z) (c : Z) (result : Z) (h_precond : maxOfThree_precond a b c) : Prop :=
  (* !benchmark @start postcond *)
  (result >= a /\ result >= b /\ result >= c) /\ (result = a \/ result = b \/ result = c)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxOfThree_postcond_satisfied (a : Z) (b : Z) (c : Z) (h_precond : maxOfThree_precond a b c) :
    maxOfThree_postcond a b c (maxOfThree a b c h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
