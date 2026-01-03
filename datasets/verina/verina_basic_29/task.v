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
Definition removeElement_precond_dec (s : (list Z)) (k : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition removeElement_precond (s : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition removeElement (s : (list Z)) (k : nat) (h_precond : removeElement_precond s k) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition removeElement_postcond_dec (s : (list Z)) (k : nat) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (s : (list Z)) (k : nat) (result : (list Z)) (h_precond : removeElement_precond s k) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (s : (list Z)) (k : nat) (h_precond : removeElement_precond s k) :
    removeElement_postcond s k (removeElement s k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
