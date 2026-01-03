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
Definition maxSubarraySum_precond_dec (numbers : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition maxSubarraySum_precond (numbers : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition maxSubarraySum (numbers : (list Z)) (h_precond : maxSubarraySum_precond numbers) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition maxSubarraySum_postcond_dec (numbers : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition maxSubarraySum_postcond (numbers : (list Z)) (result : Z) (h_precond : maxSubarraySum_precond numbers) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem maxSubarraySum_postcond_satisfied (numbers : (list Z)) (h_precond : maxSubarraySum_precond numbers) :
    maxSubarraySum_postcond numbers (maxSubarraySum numbers h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
