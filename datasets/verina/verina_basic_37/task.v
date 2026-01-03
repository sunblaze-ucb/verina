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
Definition findFirstOccurrence_precond_dec (arr : (list Z)) (target : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition findFirstOccurrence_precond (arr : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findFirstOccurrence (arr : (list Z)) (target : Z) (h_precond : findFirstOccurrence_precond arr target) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findFirstOccurrence_postcond_dec (arr : (list Z)) (target : Z) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition findFirstOccurrence_postcond (arr : (list Z)) (target : Z) (result : Z) (h_precond : findFirstOccurrence_precond arr target) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem findFirstOccurrence_postcond_satisfied (arr : (list Z)) (target : Z) (h_precond : findFirstOccurrence_precond arr target) :
    findFirstOccurrence_postcond arr target (findFirstOccurrence arr target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
