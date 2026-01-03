(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition SwapSimultaneous_precond_dec (X : Z) (Y : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition SwapSimultaneous_precond (X : Z) (Y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition SwapSimultaneous (X : Z) (Y : Z) (h_precond : SwapSimultaneous_precond X Y) : (Z  * Z) :=
  (* !benchmark @start code *)
  (0%Z, 0%Z)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SwapSimultaneous_postcond_dec (X : Z) (Y : Z) (result : (Z  * Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition SwapSimultaneous_postcond (X : Z) (Y : Z) (result : (Z  * Z)) (h_precond : SwapSimultaneous_precond X Y) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem SwapSimultaneous_postcond_satisfied (X : Z) (Y : Z) (h_precond : SwapSimultaneous_precond X Y) :
    SwapSimultaneous_postcond X Y (SwapSimultaneous X Y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.