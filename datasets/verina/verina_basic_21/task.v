(* !benchmark @start import type=task *)
Require Import Bool.
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
Definition isSublist_precond_dec (sub : (list Z)) (main : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition isSublist_precond (sub : (list Z)) (main : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isSublist (sub : (list Z)) (main : (list Z)) (h_precond : isSublist_precond sub main) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isSublist_postcond_dec (sub : (list Z)) (main : (list Z)) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition isSublist_postcond (sub : (list Z)) (main : (list Z)) (result : bool) (h_precond : isSublist_precond sub main) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem isSublist_postcond_satisfied (sub : (list Z)) (main : (list Z)) (h_precond : isSublist_precond sub main) :
    isSublist_postcond sub main (isSublist sub main h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
