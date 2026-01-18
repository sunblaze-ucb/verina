(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Reals.
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.
Open Scope R_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to convert nat to Z *)
Definition nat_to_Z (n : nat) : Z := Z.of_nat n.

(* Helper to convert Z to R *)
Definition Z_to_R (z : Z) : R := IZR z.

(* Helper to convert nat to R *)
Definition nat_to_R (n : nat) : R := INR n.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition sumAndAverage_precond_dec (n : nat) : bool :=
  (0 <? n)%nat && (n <? 9007199254740992)%nat.
(* !benchmark @end precond_aux *)

Definition sumAndAverage_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  (n > 0)%nat /\ (n < 9007199254740992)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to compute sum of first n natural numbers *)
Definition sum_first_n (n : nat) : Z :=
  let n_z := nat_to_Z n in
  (n_z * (n_z + 1) / 2)%Z.

(* Helper to compute average *)
Definition average_first_n (n : nat) : R :=
  let sum := sum_first_n n in
  let sum_r := Z_to_R sum in
  let n_r := nat_to_R n in
  (sum_r / n_r)%R.
(* !benchmark @end code_aux *)

Definition sumAndAverage (n : nat) (h_precond : sumAndAverage_precond n) : (Z  * R) :=
  (* !benchmark @start code *)
  if (n <=? 0)%nat then (0%Z, 0%R)
else
  let sum := sum_first_n n in
  let avg := average_first_n n in
  (sum, avg)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* We cannot easily provide a boolean decidable version for Real comparisons,
   so we provide a simplified version that only checks the sum part *)
Definition sumAndAverage_postcond_dec (n : nat) (result : Z * R) : bool :=
  let '(sum_val, avg_val) := result in
  if (n =? 0)%nat then
    (sum_val =? 0)%Z
  else
    let expected_sum := sum_first_n n in
    (sum_val =? expected_sum)%Z.
(* !benchmark @end postcond_aux *)

Definition sumAndAverage_postcond (n : nat) (result : (Z  * R)) (h_precond : sumAndAverage_precond n) : Prop :=
  (* !benchmark @start postcond *)
  let '(sum_val, avg_val) := result in
((n = 0%nat) -> (sum_val = 0%Z /\ avg_val = 0%R)) /\
((n > 0)%nat ->
  (sum_val = (nat_to_Z n * (nat_to_Z n + 1) / 2)%Z /\
   avg_val = (Z_to_R (nat_to_Z n * (nat_to_Z n + 1) / 2) / nat_to_R n)%R))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumAndAverage_postcond_satisfied (n : nat) (h_precond : sumAndAverage_precond n) :
    sumAndAverage_postcond n (sumAndAverage n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
