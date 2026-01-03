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
Definition elementWiseModulo_precond_dec (a : (list Z)) (b : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition elementWiseModulo_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition elementWiseModulo (a : (list Z)) (b : (list Z)) (h_precond : elementWiseModulo_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition elementWiseModulo_postcond_dec (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition elementWiseModulo_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : elementWiseModulo_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem elementWiseModulo_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : elementWiseModulo_precond a b) :
    elementWiseModulo_postcond a b (elementWiseModulo a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
