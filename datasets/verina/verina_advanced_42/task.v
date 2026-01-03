(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition maxProfit_precond_dec (prices : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition maxProfit_precond (prices : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition maxProfit (prices : (list nat)) (h_precond : maxProfit_precond prices) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition maxProfit_postcond_dec (prices : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition maxProfit_postcond (prices : (list nat)) (result : nat) (h_precond : maxProfit_precond prices) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem maxProfit_postcond_satisfied (prices : (list nat)) (h_precond : maxProfit_precond prices) :
    maxProfit_postcond prices (maxProfit prices h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
