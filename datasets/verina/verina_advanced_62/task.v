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
Definition rain_precond_dec (heights : (list (Z))) : bool := true.
(* !benchmark @end precond_aux *)

Definition rain_precond (heights : (list (Z))) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition rain (heights : (list (Z))) (h_precond : rain_precond heights) : Z :=
  (* !benchmark @start code *)
  0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition rain_postcond_dec (heights : (list (Z))) (result : Z) : bool := true.
(* !benchmark @end postcond_aux *)

Definition rain_postcond (heights : (list (Z))) (result : Z) (h_precond : rain_precond heights) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem rain_postcond_satisfied (heights : (list (Z))) (h_precond : rain_precond heights) :
    rain_postcond heights (rain heights h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
