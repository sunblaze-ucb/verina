(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No additional task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional helper definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isEven_precond_dec (n : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isEven_precond (n : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional helper definitions needed *)
(* !benchmark @end code_aux *)

Definition isEven (n : Z) (h_precond : isEven_precond n) : bool :=
  (* !benchmark @start code *)
  Z.eqb (Z.modulo n 2) 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isEven_postcond_dec (n : Z) (result : bool) : bool :=
  if result then Z.eqb (Z.modulo n 2) 0
  else negb (Z.eqb (Z.modulo n 2) 0).
(* !benchmark @end postcond_aux *)

Definition isEven_postcond (n : Z) (result : bool) (h_precond : isEven_precond n) : Prop :=
  (* !benchmark @start postcond *)
  (result = true -> (n mod 2)%Z = 0) /\ (result = false -> (n mod 2)%Z <> 0)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isEven_postcond_satisfied (n : Z) (h_precond : isEven_precond n) :
    isEven_postcond n (isEven n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
