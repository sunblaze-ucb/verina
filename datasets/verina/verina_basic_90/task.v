(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition SlopeSearch_precond_dec (a : (list (list Z))) (key : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition SlopeSearch_precond (a : (list (list Z))) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition SlopeSearch (a : (list (list Z))) (key : Z) (h_precond : SlopeSearch_precond a key) : (Z  * Z) :=
  (* !benchmark @start code *)
  (0%Z, 0%Z)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SlopeSearch_postcond_dec (a : (list (list Z))) (key : Z) (result : (Z  * Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition SlopeSearch_postcond (a : (list (list Z))) (key : Z) (result : (Z  * Z)) (h_precond : SlopeSearch_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem SlopeSearch_postcond_satisfied (a : (list (list Z))) (key : Z) (h_precond : SlopeSearch_precond a key) :
    SlopeSearch_postcond a key (SlopeSearch a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.