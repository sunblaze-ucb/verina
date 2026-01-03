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
Definition CountLessThan_precond_dec (numbers : (list Z)) (threshold : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition CountLessThan_precond (numbers : (list Z)) (threshold : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition CountLessThan (numbers : (list Z)) (threshold : Z) (h_precond : CountLessThan_precond numbers threshold) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition CountLessThan_postcond_dec (numbers : (list Z)) (threshold : Z) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition CountLessThan_postcond (numbers : (list Z)) (threshold : Z) (result : nat) (h_precond : CountLessThan_precond numbers threshold) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem CountLessThan_postcond_satisfied (numbers : (list Z)) (threshold : Z) (h_precond : CountLessThan_precond numbers threshold) :
    CountLessThan_postcond numbers threshold (CountLessThan numbers threshold h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
