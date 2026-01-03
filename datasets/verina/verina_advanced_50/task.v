(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition mergeSorted_precond_dec (a1 : (list nat)) (a2 : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition mergeSorted_precond (a1 : (list nat)) (a2 : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition mergeSorted (a1 : (list nat)) (a2 : (list nat)) (h_precond : mergeSorted_precond a1 a2) : (list nat) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition mergeSorted_postcond_dec (a1 : (list nat)) (a2 : (list nat)) (result : (list nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition mergeSorted_postcond (a1 : (list nat)) (a2 : (list nat)) (result : (list nat)) (h_precond : mergeSorted_precond a1 a2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem mergeSorted_postcond_satisfied (a1 : (list nat)) (a2 : (list nat)) (h_precond : mergeSorted_precond a1 a2) :
    mergeSorted_postcond a1 a2 (mergeSorted a1 a2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
