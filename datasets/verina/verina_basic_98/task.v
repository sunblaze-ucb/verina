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

Definition Triple_precond (x : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition Triple (x : Z) : Z :=
  (* !benchmark @start code *)
  (x * 3)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition Triple_postcond (x : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  ((result / 3)%Z =? x)%Z && ((result / 3 * 3)%Z =? result)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Triple_postcond_satisfied (x : Z) :
    Triple_precond x = true ->
    Triple_postcond x (Triple x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
