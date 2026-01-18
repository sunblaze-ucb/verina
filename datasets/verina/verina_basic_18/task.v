(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to convert nat to string *)
Fixpoint nat_to_string_aux (fuel : nat) (n : nat) (acc : string) : string :=
  match fuel with
  | 0%nat => acc
  | S fuel' =>
    match n with
    | 0%nat => acc
    | _ =>
      let digit := ascii_of_nat (Nat.modulo n 10 + 48) in
      nat_to_string_aux fuel' (Nat.div n 10) (String digit acc)
    end
  end.

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0%nat => String (ascii_of_nat 48) EmptyString
  | _ => nat_to_string_aux (S n) n EmptyString
  end.

(* Helper to convert string to list of ascii *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

(* Helper to get ascii value of '0' *)
Definition ascii_zero : nat := nat_of_ascii "0"%char.

(* Helper to convert char to digit value *)
Definition char_to_digit (c : ascii) : nat :=
  (nat_of_ascii c - ascii_zero)%nat.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition sumOfDigits_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition sumOfDigits_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sumOfDigits_loop (n : nat) (acc : nat) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => acc
  | S fuel' =>
    match n with
    | 0%nat => acc
    | _ => sumOfDigits_loop (Nat.div n 10) (acc + (Nat.modulo n 10))%nat fuel'
    end
  end.
(* !benchmark @end code_aux *)

Definition sumOfDigits (n : nat) (h_precond : sumOfDigits_precond n) : nat :=
  (* !benchmark @start code *)
  sumOfDigits_loop n 0%nat (S n)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition sumOfDigits_postcond_dec (n : nat) (result : nat) : bool :=
  let digit_sum := fold_left (fun acc c => (acc + char_to_digit c)%nat) 
                             (string_to_list (nat_to_string n)) 0%nat in
  andb (Nat.eqb (result - digit_sum)%nat 0%nat)
       (Nat.eqb (digit_sum - result)%nat 0%nat).
(* !benchmark @end postcond_aux *)

Definition sumOfDigits_postcond (n : nat) (result : nat) (h_precond : sumOfDigits_precond n) : Prop :=
  (* !benchmark @start postcond *)
  let digit_sum := fold_left (fun acc c => (acc + char_to_digit c)%nat)
                           (string_to_list (nat_to_string n)) 0%nat in
(result - digit_sum = 0)%nat /\ (digit_sum - result = 0)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem sumOfDigits_postcond_satisfied (n : nat) (h_precond : sumOfDigits_precond n) :
    sumOfDigits_postcond n (sumOfDigits n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
