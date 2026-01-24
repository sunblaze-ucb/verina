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

Definition Abs_precond (x : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition Abs (x : Z) : Z :=
  (* !benchmark @start code *)
  if (x <? 0)%Z then (-x)%Z else x
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition Abs_postcond (x : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  implb (x >=? 0)%Z (x =? result)%Z && implb (x <? 0)%Z ((x + result) =? 0)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Abs_postcond_satisfied (x : Z) :
    Abs_precond x = true ->
    Abs_postcond x (Abs x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
