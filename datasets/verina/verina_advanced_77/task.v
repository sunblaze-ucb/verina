(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition trapRainWater_precond_dec (height : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition trapRainWater_precond (height : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition trapRainWater (height : (list nat)) (h_precond : trapRainWater_precond height) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition trapRainWater_postcond_dec (height : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition trapRainWater_postcond (height : (list nat)) (result : nat) (h_precond : trapRainWater_precond height) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem trapRainWater_postcond_satisfied (height : (list nat)) (h_precond : trapRainWater_precond height) :
    trapRainWater_postcond height (trapRainWater height h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
