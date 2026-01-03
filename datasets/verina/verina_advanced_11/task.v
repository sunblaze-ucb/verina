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
Definition findMajorityElement_precond_dec (lst : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition findMajorityElement_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findMajorityElement (lst : (list Z)) (h_precond : findMajorityElement_precond lst) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findMajorityElement_postcond_dec (lst : (list Z)) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition findMajorityElement_postcond (lst : (list Z)) (result : Z) (h_precond : findMajorityElement_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem findMajorityElement_postcond_satisfied (lst : (list Z)) (h_precond : findMajorityElement_precond lst) :
    findMajorityElement_postcond lst (findMajorityElement lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
