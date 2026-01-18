(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition Triple_precond_dec (x : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition Triple_precond (x : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions needed *)
(* !benchmark @end code_aux *)

Definition Triple (x : Z) (h_precond : Triple_precond x) : Z :=
  (* !benchmark @start code *)
  if (x =? 0) then 0 else
  let y := 2 * x in
  x + y
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Triple_postcond_dec (x : Z) (result : Z) : bool :=
  if (result =? 0) then (x =? 0)
  else
    (result / 3 =? x) && (result / 3 * 3 =? result).
(* !benchmark @end postcond_aux *)

Definition Triple_postcond (x : Z) (result : Z) (h_precond : Triple_precond x) : Prop :=
  (* !benchmark @start postcond *)
  result / 3 = x /\ result / 3 * 3 = result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Triple_postcond_satisfied (x : Z) (h_precond : Triple_precond x) :
    Triple_postcond x (Triple x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
