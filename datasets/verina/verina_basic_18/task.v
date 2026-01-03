(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition sumOfDigits_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition sumOfDigits_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition sumOfDigits (n : nat) (h_precond : sumOfDigits_precond n) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition sumOfDigits_postcond_dec (n : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition sumOfDigits_postcond (n : nat) (result : nat) (h_precond : sumOfDigits_precond n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem sumOfDigits_postcond_satisfied (n : nat) (h_precond : sumOfDigits_precond n) :
    sumOfDigits_postcond n (sumOfDigits n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
