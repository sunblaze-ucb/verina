(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition solution_precond_dec (nums : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition solution_precond (nums : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition solution (nums : (list nat)) (h_precond : solution_precond nums) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition solution_postcond_dec (nums : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition solution_postcond (nums : (list nat)) (result : nat) (h_precond : solution_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem solution_postcond_satisfied (nums : (list nat)) (h_precond : solution_precond nums) :
    solution_postcond nums (solution nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
