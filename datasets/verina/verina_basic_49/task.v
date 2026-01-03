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
Definition findFirstOdd_precond_dec (a : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition findFirstOdd_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findFirstOdd (a : (list Z)) (h_precond : findFirstOdd_precond a) : (option nat) :=
  (* !benchmark @start code *)
  None
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findFirstOdd_postcond_dec (a : (list Z)) (result : (option nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition findFirstOdd_postcond (a : (list Z)) (result : (option nat)) (h_precond : findFirstOdd_precond a) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem findFirstOdd_postcond_satisfied (a : (list Z)) (h_precond : findFirstOdd_precond a) :
    findFirstOdd_postcond a (findFirstOdd a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
