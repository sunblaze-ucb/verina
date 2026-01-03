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
Definition secondSmallest_precond_dec (s : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition secondSmallest_precond (s : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition secondSmallest (s : (list Z)) (h_precond : secondSmallest_precond s) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition secondSmallest_postcond_dec (s : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition secondSmallest_postcond (s : (list Z)) (result : Z) (h_precond : secondSmallest_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem secondSmallest_postcond_satisfied (s : (list Z)) (h_precond : secondSmallest_precond s) :
    secondSmallest_postcond s (secondSmallest s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
