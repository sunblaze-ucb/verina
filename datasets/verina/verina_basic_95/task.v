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
Definition swap_precond_dec (arr : (list Z)) (i : Z) (j : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition swap_precond (arr : (list Z)) (i : Z) (j : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition swap (arr : (list Z)) (i : Z) (j : Z) (h_precond : swap_precond arr i j) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition swap_postcond_dec (arr : (list Z)) (i : Z) (j : Z) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition swap_postcond (arr : (list Z)) (i : Z) (j : Z) (result : (list Z)) (h_precond : swap_precond arr i j) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem swap_postcond_satisfied (arr : (list Z)) (i : Z) (j : Z) (h_precond : swap_precond arr i j) :
    swap_postcond arr i j (swap arr i j h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
