(* !benchmark @start import type=task *)
Require Import Bool.
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
Definition isGreater_precond_dec (n : Z) (a : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition isGreater_precond (n : Z) (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isGreater (n : Z) (a : (list Z)) (h_precond : isGreater_precond n a) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isGreater_postcond_dec (n : Z) (a : (list Z)) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition isGreater_postcond (n : Z) (a : (list Z)) (result : bool) (h_precond : isGreater_precond n a) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem isGreater_postcond_satisfied (n : Z) (a : (list Z)) (h_precond : isGreater_precond n a) :
    isGreater_postcond n a (isGreater n a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
