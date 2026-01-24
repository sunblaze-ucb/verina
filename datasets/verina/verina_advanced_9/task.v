(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint sumOfDigits_go (n acc : nat) (fuel : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (n =? 0)%nat then acc
    else sumOfDigits_go (n / 10)%nat (acc + (n mod 10))%nat fuel'
  end.

Definition sumOfDigits (x : nat) : nat :=
  sumOfDigits_go x 0 (x + 1).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition countSumDivisibleBy_precond (n : nat) (d : nat) : bool :=
  (* !benchmark @start precond *)
  (0 <? d)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isSumDivisibleBy (x : nat) (d : nat) : bool :=
  ((sumOfDigits x) mod d =? 0)%nat.

Fixpoint countSumDivisibleBy_go (i acc : nat) (d : nat) : nat :=
  match i with
  | O => acc
  | S i' =>
    let acc' := if isSumDivisibleBy i' d then (acc + 1)%nat else acc in
    countSumDivisibleBy_go i' acc' d
  end.
(* !benchmark @end code_aux *)

Definition countSumDivisibleBy (n : nat) (d : nat) : nat :=
  (* !benchmark @start code *)
  countSumDivisibleBy_go n 0 d
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition checkCondition (x : nat) (n : nat) (d : nat) : bool :=
  (x <? n)%nat && ((sumOfDigits x) mod d =? 0)%nat.

Definition countFiltered (n : nat) (d : nat) : nat :=
  length (filter (fun x => checkCondition x n d) (seq 0 n)).
(* !benchmark @end postcond_aux *)

Definition countSumDivisibleBy_postcond (n : nat) (d : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  ((countFiltered n d - result =? 0)%nat && (result <=? countFiltered n d)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem countSumDivisibleBy_postcond_satisfied (n : nat) (d : nat) :
    countSumDivisibleBy_precond n d = true ->
    countSumDivisibleBy_postcond n d (countSumDivisibleBy n d) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
