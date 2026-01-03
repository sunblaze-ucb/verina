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
Definition replace_precond_dec (arr : (list Z)) (k : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition replace_precond (arr : (list Z)) (k : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition replace (arr : (list Z)) (k : Z) (h_precond : replace_precond arr k) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition replace_postcond_dec (arr : (list Z)) (k : Z) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition replace_postcond (arr : (list Z)) (k : Z) (result : (list Z)) (h_precond : replace_precond arr k) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem replace_postcond_satisfied (arr : (list Z)) (k : Z) (h_precond : replace_precond arr k) :
    replace_postcond arr k (replace arr k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
