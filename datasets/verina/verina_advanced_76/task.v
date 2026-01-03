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
Definition topKFrequent_precond_dec (nums : (list Z)) (k : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition topKFrequent_precond (nums : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition topKFrequent (nums : (list Z)) (k : nat) (h_precond : topKFrequent_precond nums k) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition topKFrequent_postcond_dec (nums : (list Z)) (k : nat) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition topKFrequent_postcond (nums : (list Z)) (k : nat) (result : (list Z)) (h_precond : topKFrequent_precond nums k) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem topKFrequent_postcond_satisfied (nums : (list Z)) (k : nat) (h_precond : topKFrequent_precond nums k) :
    topKFrequent_postcond nums k (topKFrequent nums k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
