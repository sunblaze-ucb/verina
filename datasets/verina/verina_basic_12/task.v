(* !benchmark @start import type=task *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition cubeSurfaceArea_precond (size : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition cubeSurfaceArea (size : nat) : nat :=
  (* !benchmark @start code *)
  (6 * size * size)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition cubeSurfaceArea_postcond (size : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result =? 6 * size * size)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem cubeSurfaceArea_postcond_satisfied (size : nat) :
    cubeSurfaceArea_precond size = true ->
    cubeSurfaceArea_postcond size (cubeSurfaceArea size) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
