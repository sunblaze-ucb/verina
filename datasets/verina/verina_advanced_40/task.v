(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition maxOfList_precond_dec (lst : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition maxOfList_precond (lst : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition maxOfList (lst : (list nat)) (h_precond : maxOfList_precond lst) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition maxOfList_postcond_dec (lst : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition maxOfList_postcond (lst : (list nat)) (result : nat) (h_precond : maxOfList_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem maxOfList_postcond_satisfied (lst : (list nat)) (h_precond : maxOfList_precond lst) :
    maxOfList_postcond lst (maxOfList lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
