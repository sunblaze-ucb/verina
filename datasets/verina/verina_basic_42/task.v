(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition countDigits_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition countDigits_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition countDigits (s : string) (h_precond : countDigits_precond s) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition countDigits_postcond_dec (s : string) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition countDigits_postcond (s : string) (result : nat) (h_precond : countDigits_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem countDigits_postcond_satisfied (s : string) (h_precond : countDigits_precond s) :
    countDigits_postcond s (countDigits s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
