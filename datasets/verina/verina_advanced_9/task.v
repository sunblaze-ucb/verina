(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition countSumDivisibleBy_precond_dec (n : nat) (d : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition countSumDivisibleBy_precond (n : nat) (d : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition countSumDivisibleBy (n : nat) (d : nat) (h_precond : countSumDivisibleBy_precond n d) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition countSumDivisibleBy_postcond_dec (n : nat) (d : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition countSumDivisibleBy_postcond (n : nat) (d : nat) (result : nat) (h_precond : countSumDivisibleBy_precond n d) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem countSumDivisibleBy_postcond_satisfied (n : nat) (d : nat) (h_precond : countSumDivisibleBy_precond n d) :
    countSumDivisibleBy_postcond n d (countSumDivisibleBy n d h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
