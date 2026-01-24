(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition myMin_precond (a : Z) (b : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition myMin (a : Z) (b : Z) : Z :=
  (* !benchmark @start code *)
  if (a <=? b)%Z then a else b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition myMin_postcond (a : Z) (b : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  ((result <=? a)%Z && (result <=? b)%Z) && ((result =? a)%Z || (result =? b)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem myMin_postcond_satisfied (a : Z) (b : Z) :
    myMin_precond a b = true ->
    myMin_postcond a b (myMin a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
