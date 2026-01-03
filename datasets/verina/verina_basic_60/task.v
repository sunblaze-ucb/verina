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
Definition FindEvenNumbers_precond_dec (arr : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition FindEvenNumbers_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition FindEvenNumbers (arr : (list Z)) (h_precond : FindEvenNumbers_precond arr) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition FindEvenNumbers_postcond_dec (arr : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition FindEvenNumbers_postcond (arr : (list Z)) (result : (list Z)) (h_precond : FindEvenNumbers_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem FindEvenNumbers_postcond_satisfied (arr : (list Z)) (h_precond : FindEvenNumbers_precond arr) :
    FindEvenNumbers_postcond arr (FindEvenNumbers arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
