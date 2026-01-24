(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Bool.
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

Definition hasOppositeSign_precond (a : Z) (b : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition hasOppositeSign (a : Z) (b : Z) : bool :=
  (* !benchmark @start code *)
  (a * b <? 0)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition hasOppositeSign_postcond (a : Z) (b : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  (implb (((a <? 0) && (0 <? b)) || ((0 <? a) && (b <? 0))) result) &&
  (implb (negb (((a <? 0) && (0 <? b)) || ((0 <? a) && (b <? 0)))) (negb result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasOppositeSign_postcond_satisfied (a : Z) (b : Z) :
    hasOppositeSign_precond a b = true ->
    hasOppositeSign_postcond a b (hasOppositeSign a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
