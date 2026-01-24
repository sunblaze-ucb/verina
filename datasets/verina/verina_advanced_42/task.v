(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition maxProfit_precond (prices : (list nat)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition updateMinAndProfit (price : nat) (minSoFar : nat) (maxProfit : nat) : (nat * nat) :=
  let newMin := Nat.min minSoFar price in
  let profit := if (minSoFar <? price)%nat then price - minSoFar else 0%nat in
  let newMaxProfit := Nat.max maxProfit profit in
  (newMin, newMaxProfit).

Fixpoint maxProfitAux (prices : list nat) (minSoFar : nat) (maxProfit : nat) : nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let '(newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit in
    maxProfitAux ps newMin newProfit
  end.
(* !benchmark @end code_aux *)

Definition maxProfit (prices : (list nat)) : nat :=
  (* !benchmark @start code *)
  match prices with
  | [] => 0%nat
  | p :: ps => maxProfitAux ps p 0%nat
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition zipIdx {A : Type} (l : list A) : list (A * nat) :=
  let fix aux (l : list A) (idx : nat) : list (A * nat) :=
    match l with
    | [] => []
    | x :: xs => (x, idx) :: aux xs (S idx)
    end
  in aux l 0%nat.

Definition pairwise_profit_le (pairs : list (nat * nat)) (res : nat) : bool :=
  forallb (fun pi_i =>
    let '(pi, i) := pi_i in
    forallb (fun pj_j =>
      let '(pj, j) := pj_j in
      implb (i <? j)%nat ((pj - pi) <=? res)%nat
    ) pairs
  ) pairs.

Definition no_profitable_transaction (pairs : list (nat * nat)) : bool :=
  forallb (fun pi_i =>
    let '(pi, i) := pi_i in
    forallb (fun pj_j =>
      let '(pj, j) := pj_j in
      orb (j <=? i)%nat (pj <=? pi)%nat
    ) pairs
  ) pairs.

Definition exists_transaction_with_profit (pairs : list (nat * nat)) (res : nat) : bool :=
  existsb (fun pi_i =>
    let '(pi, i) := pi_i in
    existsb (fun pj_j =>
      let '(pj, j) := pj_j in
      andb (i <? j)%nat ((pj - pi) =? res)%nat
    ) pairs
  ) pairs.
(* !benchmark @end postcond_aux *)

Definition maxProfit_postcond (prices : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let pairs := zipIdx prices in
    andb (andb (pairwise_profit_le pairs result)
               (implb (result =? 0)%nat (orb ((length prices <=? 1)%nat) (no_profitable_transaction pairs))))
         (implb (1 <=? result)%nat (exists_transaction_with_profit pairs result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxProfit_postcond_satisfied (prices : (list nat)) :
    maxProfit_precond prices = true ->
    maxProfit_postcond prices (maxProfit prices) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
