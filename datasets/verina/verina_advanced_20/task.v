(* !benchmark @start import type=task *)
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Nat.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isItEight_precond_dec (n : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition isItEight_precond (n : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Require Import Recdef.

Function hasDigitEight (m : nat) {measure (fun x => x) m} : bool :=
  match m with
  | 0%nat => false
  | _ => if Nat.eqb (m mod 10)%nat 8%nat then true
         else hasDigitEight (m / 10)%nat
  end.
Proof.
  intros.
  apply Nat.div_lt; lia.
Defined.
(* !benchmark @end code_aux *)

Definition isItEight (n : Z) (h_precond : isItEight_precond n) : bool :=
  (* !benchmark @start code *)
  let absN := Z.abs_nat n in
  (Z.eqb (n mod 8) 0) || hasDigitEight absN
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isItEight_postcond_dec (n : Z) (result : bool) : bool :=
  let absN := Z.abs_nat n in
  Bool.eqb ((Z.eqb (n mod 8) 0) || 
            (let fix check_digit (fuel : nat) :=
              match fuel with
              | 0%nat => false
              | S fuel' => 
                  if Nat.eqb ((absN / (Nat.pow 10 fuel')) mod 10)%nat 8%nat then true
                  else check_digit fuel'
              end
            in check_digit absN)) result.
(* !benchmark @end postcond_aux *)

Definition isItEight_postcond (n : Z) (result : bool) (h_precond : isItEight_precond n) : Prop :=
  (* !benchmark @start postcond *)
  let absN := Z.abs_nat n in
  ((n mod 8 = 0) \/ (exists i : nat, ((Z.of_nat absN) / (10 ^ (Z.of_nat i))) mod 10 = 8)) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isItEight_postcond_satisfied (n : Z) (h_precond : isItEight_precond n) :
    isItEight_postcond n (isItEight n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
