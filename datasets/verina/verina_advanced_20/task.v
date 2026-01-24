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

Definition isItEight_precond (n : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint hasDigitEight (fuel : nat) (m : Z) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (m <=? 0)%Z then false
    else if ((m mod 10) =? 8)%Z then true
    else hasDigitEight fuel' (m / 10)
  end.
(* !benchmark @end code_aux *)

Definition isItEight (n : Z) : bool :=
  (* !benchmark @start code *)
  let absN := Z.abs n in
  ((n mod 8 =? 0)%Z || hasDigitEight 100 absN)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint hasDigitEightAtPos (fuel : nat) (absN : Z) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if ((absN mod 10) =? 8)%Z then true
    else if (absN <=? 0)%Z then false
    else hasDigitEightAtPos fuel' (absN / 10)
  end.

Definition existsDigitEight (absN : Z) : bool :=
  hasDigitEightAtPos 100 absN.
(* !benchmark @end postcond_aux *)

Definition isItEight_postcond (n : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let absN := Z.abs n in
  Bool.eqb ((n mod 8 =? 0)%Z || existsDigitEight absN) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isItEight_postcond_satisfied (n : Z) :
    isItEight_precond n = true ->
    isItEight_postcond n (isItEight n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
