(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition DivisionFunction_precond (x : nat) (y : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition divMod (x y : nat) : Z * Z :=
  let q : Z := Z.of_nat (x / y) in
  let r : Z := Z.of_nat (x mod y) in
  (r, q).
(* !benchmark @end code_aux *)

Definition DivisionFunction (x : nat) (y : nat) : (Z  * Z) :=
  (* !benchmark @start code *)
  if (y =? 0)%nat then (Z.of_nat x, 0) else divMod x y
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition DivisionFunction_postcond (x : nat) (y : nat) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  let '(r, q) := result in
    (implb (y =? 0)%nat ((r =? Z.of_nat x) && (q =? 0))) &&
    (implb (negb (y =? 0)%nat) 
      ((q * Z.of_nat y + r =? Z.of_nat x) && 
       (0 <=? r) && (r <? Z.of_nat y) && 
       (0 <=? q)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem DivisionFunction_postcond_satisfied (x : nat) (y : nat) :
    DivisionFunction_precond x y = true ->
    DivisionFunction_postcond x y (DivisionFunction x y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
