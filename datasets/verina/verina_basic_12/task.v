(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition cubeSurfaceArea_precond_dec (size : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition cubeSurfaceArea_precond (size : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition cubeSurfaceArea (size : nat) (h_precond : cubeSurfaceArea_precond size) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition cubeSurfaceArea_postcond_dec (size : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition cubeSurfaceArea_postcond (size : nat) (result : nat) (h_precond : cubeSurfaceArea_precond size) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem cubeSurfaceArea_postcond_satisfied (size : nat) (h_precond : cubeSurfaceArea_precond size) :
    cubeSurfaceArea_postcond size (cubeSurfaceArea size h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
