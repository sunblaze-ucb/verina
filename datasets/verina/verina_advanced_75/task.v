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
Definition task_code_precond_dec (sequence : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition task_code_precond (sequence : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition task_code (sequence : (list Z)) (h_precond : task_code_precond sequence) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition task_code_postcond_dec (sequence : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition task_code_postcond (sequence : (list Z)) (result : Z) (h_precond : task_code_precond sequence) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem task_code_postcond_satisfied (sequence : (list Z)) (h_precond : task_code_precond sequence) :
    task_code_postcond sequence (task_code sequence h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
