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
Definition BubbleSort_precond_dec (a : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition BubbleSort_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition BubbleSort (a : (list Z)) (h_precond : BubbleSort_precond a) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition BubbleSort_postcond_dec (a : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition BubbleSort_postcond (a : (list Z)) (result : (list Z)) (h_precond : BubbleSort_precond a) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem BubbleSort_postcond_satisfied (a : (list Z)) (h_precond : BubbleSort_precond a) :
    BubbleSort_postcond a (BubbleSort a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
