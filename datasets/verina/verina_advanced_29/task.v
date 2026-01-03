(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition longestGoodSubarray_precond_dec (nums : (list nat)) (k : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestGoodSubarray_precond (nums : (list nat)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition longestGoodSubarray (nums : (list nat)) (k : nat) (h_precond : longestGoodSubarray_precond nums k) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestGoodSubarray_postcond_dec (nums : (list nat)) (k : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition longestGoodSubarray_postcond (nums : (list nat)) (k : nat) (result : nat) (h_precond : longestGoodSubarray_precond nums k) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem longestGoodSubarray_postcond_satisfied (nums : (list nat)) (k : nat) (h_precond : longestGoodSubarray_precond nums k) :
    longestGoodSubarray_postcond nums k (longestGoodSubarray nums k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
