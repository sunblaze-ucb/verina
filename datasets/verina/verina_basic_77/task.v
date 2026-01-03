(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition modify_array_element_precond_dec (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition modify_array_element_precond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition modify_array_element (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (h_precond : modify_array_element_precond arr index1 index2 val) : (list (list nat)) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition modify_array_element_postcond_dec (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (result : (list (list nat))) : bool := true.
(* !benchmark @end postcond_aux *)

Definition modify_array_element_postcond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (result : (list (list nat))) (h_precond : modify_array_element_precond arr index1 index2 val) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem modify_array_element_postcond_satisfied (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (h_precond : modify_array_element_precond arr index1 index2 val) :
    modify_array_element_postcond arr index1 index2 val (modify_array_element arr index1 index2 val h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
