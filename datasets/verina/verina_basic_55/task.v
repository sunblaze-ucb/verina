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

Definition Compare_precond (a : Z) (b : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition Compare (a : Z) (b : Z) : bool :=
  (* !benchmark @start code *)
  if (a =? b)%Z then true else false
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition Compare_postcond (a : Z) (b : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  implb (a =? b)%Z (Bool.eqb result true) && implb (negb (a =? b)%Z) (Bool.eqb result false)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Compare_postcond_satisfied (a : Z) (b : Z) :
    Compare_precond a b = true ->
    Compare_postcond a b (Compare a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
