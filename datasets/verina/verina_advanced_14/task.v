(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import PeanoNat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition ifPowerOfFour_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint helper (fuel : nat) (n : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match n with
    | O => false
    | S m =>
      match m with
      | O => true
      | S l =>
        if ((l + 2) mod 4 =? 0)%nat then
          helper fuel' ((l + 2) / 4)
        else
          false
      end
    end
  end.
(* !benchmark @end code_aux *)

Definition ifPowerOfFour (n : nat) : bool :=
  (* !benchmark @start code *)
  helper n n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint power4 (m : nat) : nat :=
  match m with
  | O => 1%nat
  | S m' => (4 * power4 m')%nat
  end.

Fixpoint existsPower4 (fuel : nat) (n : nat) : bool :=
  match fuel with
  | O => (n =? 1)%nat
  | S fuel' => 
    if (power4 fuel =? n)%nat then true
    else existsPower4 fuel' n
  end.
(* !benchmark @end postcond_aux *)

Definition ifPowerOfFour_postcond (n : nat) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb result (existsPower4 n n)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ifPowerOfFour_postcond_satisfied (n : nat) :
    ifPowerOfFour_precond n = true ->
    ifPowerOfFour_postcond n (ifPowerOfFour n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
