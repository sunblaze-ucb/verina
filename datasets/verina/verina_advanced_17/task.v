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
Definition insertionSort_precond_dec (l : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition insertionSort_precond (l : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition insertionSort (l : (list Z)) (h_precond : insertionSort_precond l) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition insertionSort_postcond_dec (l : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition insertionSort_postcond (l : (list Z)) (result : (list Z)) (h_precond : insertionSort_precond l) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem insertionSort_postcond_satisfied (l : (list Z)) (h_precond : insertionSort_precond l) :
    insertionSort_postcond l (insertionSort l h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
