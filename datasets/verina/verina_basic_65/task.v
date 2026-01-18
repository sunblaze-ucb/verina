(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SquareRoot_precond_dec (N : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition SquareRoot_precond (N : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint boundedLoop (N : nat) (bound : nat) (r : nat) : nat :=
  match bound with
  | 0 => r
  | S bound' =>
      if Nat.leb ((r + 1) * (r + 1)) N then
        boundedLoop N bound' (r + 1)
      else
        r
  end.
(* !benchmark @end code_aux *)

Definition SquareRoot (N : nat) (h_precond : SquareRoot_precond N) : nat :=
  (* !benchmark @start code *)
  boundedLoop N (N + 1) 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SquareRoot_postcond_dec (N : nat) (result : nat) : bool :=
  Nat.leb (result * result) N && Nat.ltb N ((result + 1) * (result + 1)).
(* !benchmark @end postcond_aux *)

Definition SquareRoot_postcond (N : nat) (result : nat) (h_precond : SquareRoot_precond N) : Prop :=
  (* !benchmark @start postcond *)
  result * result <= N /\ N < (result + 1) * (result + 1)
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
