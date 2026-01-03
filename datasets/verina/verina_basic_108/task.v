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
Definition below_zero_precond_dec (operations : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition below_zero_precond (operations : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition below_zero (operations : (list Z)) (h_precond : below_zero_precond operations) : (list (Z  * bool)) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition below_zero_postcond_dec (operations : (list Z)) (result : (list (Z  * bool))) : bool := true.
(* !benchmark @end postcond_aux *)

Definition below_zero_postcond (operations : (list Z)) (result : (list (Z  * bool))) (h_precond : below_zero_precond operations) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem below_zero_postcond_satisfied (operations : (list Z)) (h_precond : below_zero_precond operations) :
    below_zero_postcond operations (below_zero operations h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
