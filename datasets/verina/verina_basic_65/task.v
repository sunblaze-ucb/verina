(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition SquareRoot_precond_dec (N : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition SquareRoot_precond (N : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition SquareRoot (N : nat) (h_precond : SquareRoot_precond N) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SquareRoot_postcond_dec (N : nat) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition SquareRoot_postcond (N : nat) (result : nat) (h_precond : SquareRoot_precond N) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem SquareRoot_postcond_satisfied (N : nat) (h_precond : SquareRoot_precond N) :
    SquareRoot_postcond N (SquareRoot N h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
