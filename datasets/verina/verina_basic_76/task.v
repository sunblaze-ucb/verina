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

Definition myMin_precond (x : Z) (y : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition myMin (x : Z) (y : Z) : Z :=
  (* !benchmark @start code *)
  if (x <? y)%Z then x else y
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition myMin_postcond (x : Z) (y : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  implb (x <=? y)%Z (result =? x)%Z && implb (x >? y)%Z (result =? y)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem myMin_postcond_satisfied (x : Z) (y : Z) :
    myMin_precond x y = true ->
    myMin_postcond x y (myMin x y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
