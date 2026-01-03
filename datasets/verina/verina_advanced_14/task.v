(* !benchmark @start import type=task *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition ifPowerOfFour_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition ifPowerOfFour_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition ifPowerOfFour (n : nat) (h_precond : ifPowerOfFour_precond n) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ifPowerOfFour_postcond_dec (n : nat) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition ifPowerOfFour_postcond (n : nat) (result : bool) (h_precond : ifPowerOfFour_precond n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem ifPowerOfFour_postcond_satisfied (n : nat) (h_precond : ifPowerOfFour_precond n) :
    ifPowerOfFour_postcond n (ifPowerOfFour n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
