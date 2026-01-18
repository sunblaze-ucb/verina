(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint sumOfDigits_go (fuel : nat) (n : nat) (acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
      match n with
      | 0 => acc
      | _ => sumOfDigits_go fuel' (n / 10) (acc + (n mod 10))
      end
  end.

Definition sumOfDigits (x : nat) : nat :=
  sumOfDigits_go x x 0.

Definition isSumDivisibleBy (x : nat) (d : nat) : bool :=
  Nat.eqb ((sumOfDigits x) mod d) 0.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition countSumDivisibleBy_precond_dec (n : nat) (d : nat) : bool :=
  Nat.ltb 0 d.
(* !benchmark @end precond_aux *)

Definition countSumDivisibleBy_precond (n : nat) (d : nat) : Prop :=
  (* !benchmark @start precond *)
  (d > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countSumDivisibleBy_go (i : nat) (acc : nat) (d : nat) : nat :=
  match i with
  | 0 => acc
  | S i' =>
      let acc' := if isSumDivisibleBy i' d then (acc + 1)%nat else acc in
      countSumDivisibleBy_go i' acc' d
  end.
(* !benchmark @end code_aux *)

Definition countSumDivisibleBy (n : nat) (d : nat) (h_precond : countSumDivisibleBy_precond n d) : nat :=
  (* !benchmark @start code *)
  countSumDivisibleBy_go n 0 d
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition countSumDivisibleBy_postcond_dec (n : nat) (d : nat) (result : nat) : bool :=
  let expected := length (filter (fun x => andb (x <? n) (Nat.eqb ((sumOfDigits x) mod d) 0)) (seq 0 n)) in
  andb (Nat.eqb (expected - result) 0) (result <=? expected).
(* !benchmark @end postcond_aux *)

Definition countSumDivisibleBy_postcond (n : nat) (d : nat) (result : nat) (h_precond : countSumDivisibleBy_precond n d) : Prop :=
  (* !benchmark @start postcond *)
  (length (filter (fun x => andb (x <? n) (Nat.eqb ((sumOfDigits x) mod d) 0)) (seq 0 n)) - result = 0)%nat /\
(result <= length (filter (fun x => andb (x <? n) (Nat.eqb ((sumOfDigits x) mod d) 0)) (seq 0 n)))%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem countSumDivisibleBy_postcond_satisfied (n : nat) (d : nat) (h_precond : countSumDivisibleBy_precond n d) :
    countSumDivisibleBy_postcond n d (countSumDivisibleBy n d h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
