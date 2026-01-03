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
Definition rotate_precond_dec (a : (list Z)) (offset : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition rotate_precond (a : (list Z)) (offset : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition rotate (a : (list Z)) (offset : Z) (h_precond : rotate_precond a offset) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition rotate_postcond_dec (a : (list Z)) (offset : Z) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition rotate_postcond (a : (list Z)) (offset : Z) (result : (list Z)) (h_precond : rotate_precond a offset) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem rotate_postcond_satisfied (a : (list Z)) (offset : Z) (h_precond : rotate_precond a offset) :
    rotate_postcond a offset (rotate a offset h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
