(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition lastDigit_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition lastDigit_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition lastDigit (n : nat) (h_precond : lastDigit_precond n) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition lastDigit_postcond_dec (n : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition lastDigit_postcond (n : nat) (result : nat) (h_precond : lastDigit_precond n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem lastDigit_postcond_satisfied (n : nat) (h_precond : lastDigit_precond n) :
    lastDigit_postcond n (lastDigit n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
