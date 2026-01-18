(* !benchmark @start import type=task *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Lia.

Fixpoint countDigits_go (fuel n acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' => 
      match n with
      | 0 => acc
      | _ => countDigits_go fuel' (n / 10) (acc + 1)
      end
  end.

Definition countDigits (n : nat) : nat :=
  countDigits_go (S n) n (if Nat.eqb n 0 then 1 else 0).

Fixpoint sumPowers_go (fuel n acc k : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
      match n with
      | 0 => acc
      | _ => 
          let digit := n mod 10 in
          sumPowers_go fuel' (n / 10) (acc + digit ^ k) k
      end
  end.

Definition sumPowers (n k : nat) : nat :=
  sumPowers_go (S n) n 0 k.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isArmstrong_precond_dec (n : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition isArmstrong_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code auxiliaries needed *)
(* !benchmark @end code_aux *)

Definition isArmstrong (n : nat) (h_precond : isArmstrong_precond n) : bool :=
  (* !benchmark @start code *)
  let k := countDigits n in
Nat.eqb (sumPowers n k) n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint char_to_nat (c : ascii) : nat :=
  match c with
  | "0"%char => 0
  | "1"%char => 1
  | "2"%char => 2
  | "3"%char => 3
  | "4"%char => 4
  | "5"%char => 5
  | "6"%char => 6
  | "7"%char => 7
  | "8"%char => 8
  | "9"%char => 9
  | _ => 0
  end.

Fixpoint string_to_list_char (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list_char s'
  end.

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0"
  | _ => "0" (* placeholder, full implementation omitted for brevity *)
  end.

Definition n' (n : nat) : nat :=
  let k := countDigits n in
  let digits := map char_to_nat (string_to_list_char (nat_to_string n)) in
  fold_left (fun acc d => acc + d ^ k) digits 0.

Definition isArmstrong_postcond_dec (n : nat) (result : bool) : bool :=
  let n_val := n' n in
  if result then Nat.eqb n n_val
  else negb (Nat.eqb n n_val).
(* !benchmark @end postcond_aux *)

Definition isArmstrong_postcond (n : nat) (result : bool) (h_precond : isArmstrong_precond n) : Prop :=
  (* !benchmark @start postcond *)
  let n_val := n' n in
  (result = true -> n = n_val) /\
  (result = false -> n <> n_val)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isArmstrong_postcond_satisfied (n : nat) (h_precond : isArmstrong_precond n) :
    isArmstrong_postcond n (isArmstrong n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
