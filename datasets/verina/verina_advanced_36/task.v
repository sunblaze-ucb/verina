(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition majorityElement_precond_dec (xs : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (xs : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition majorityElement (xs : (list nat)) (h_precond : majorityElement_precond xs) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition majorityElement_postcond_dec (xs : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (xs : (list nat)) (result : nat) (h_precond : majorityElement_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (xs : (list nat)) (h_precond : majorityElement_precond xs) :
    majorityElement_postcond xs (majorityElement xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
