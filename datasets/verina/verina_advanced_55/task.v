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
Definition mostFrequent_precond_dec (xs : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition mostFrequent_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition mostFrequent (xs : (list Z)) (h_precond : mostFrequent_precond xs) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition mostFrequent_postcond_dec (xs : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition mostFrequent_postcond (xs : (list Z)) (result : Z) (h_precond : mostFrequent_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem mostFrequent_postcond_satisfied (xs : (list Z)) (h_precond : mostFrequent_precond xs) :
    mostFrequent_postcond xs (mostFrequent xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
