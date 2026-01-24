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

Definition ComputeIsEven_precond (x : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition ComputeIsEven (x : Z) : bool :=
  (* !benchmark @start code *)
  if (x mod 2 =? 0)%Z then true else false
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint existsZ_range_fuel (fuel : nat) (lo hi : Z) (f : Z -> bool) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (lo <? hi)%Z then
      f lo || existsZ_range_fuel fuel' (lo + 1) hi f
    else
      false
  end.

Definition existsZ_range (lo hi : Z) (f : Z -> bool) : bool :=
  let diff := (hi - lo)%Z in
  let fuel := Z.to_nat (if (diff <? 0)%Z then 0 else diff + 1) in
  existsZ_range_fuel fuel lo hi f.

Definition existsZ_divisor (x : Z) (f : Z -> bool) : bool :=
  let bound := Z.abs x + 1 in
  existsZ_range (-bound) (bound + 1) f.
(* !benchmark @end postcond_aux *)

Definition ComputeIsEven_postcond (x : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let check_even := existsZ_divisor x (fun k => (x =? 2 * k)%Z) in
  implb result check_even && implb check_even result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ComputeIsEven_postcond_satisfied (x : Z) :
    ComputeIsEven_precond x = true ->
    ComputeIsEven_postcond x (ComputeIsEven x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
