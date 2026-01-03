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
Definition kthElement_precond_dec (arr : (list Z)) (k : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition kthElement_precond (arr : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition kthElement (arr : (list Z)) (k : nat) (h_precond : kthElement_precond arr k) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition kthElement_postcond_dec (arr : (list Z)) (k : nat) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition kthElement_postcond (arr : (list Z)) (k : nat) (result : Z) (h_precond : kthElement_precond arr k) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem kthElement_postcond_satisfied (arr : (list Z)) (k : nat) (h_precond : kthElement_precond arr k) :
    kthElement_postcond arr k (kthElement arr k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
