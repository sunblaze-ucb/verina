(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition removeElement_precond_dec (lst : (list nat)) (target : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition removeElement_precond (lst : (list nat)) (target : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition removeElement (lst : (list nat)) (target : nat) (h_precond : removeElement_precond lst target) : (list nat) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition removeElement_postcond_dec (lst : (list nat)) (target : nat) (result : (list nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (lst : (list nat)) (target : nat) (result : (list nat)) (h_precond : removeElement_precond lst target) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (lst : (list nat)) (target : nat) (h_precond : removeElement_precond lst target) :
    removeElement_postcond lst target (removeElement lst target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
