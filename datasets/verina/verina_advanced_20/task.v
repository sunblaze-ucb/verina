(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition isItEight_precond_dec (n : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition isItEight_precond (n : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isItEight (n : Z) (h_precond : isItEight_precond n) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isItEight_postcond_dec (n : Z) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition isItEight_postcond (n : Z) (result : bool) (h_precond : isItEight_precond n) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem isItEight_postcond_satisfied (n : Z) (h_precond : isItEight_precond n) :
    isItEight_postcond n (isItEight n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
