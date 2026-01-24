(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition concat_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (fuel : nat) (i : nat) (n : nat) (a : list Z) (b : list Z) (c : list Z) : list Z :=
  match fuel with
  | O => c
  | S fuel' =>
    if (i <? n)%nat then
      let value := if (i <? length a)%nat then nth i a 0%Z else nth (i - length a) b 0%Z in
      let c' := firstn i c ++ [value] ++ skipn (S i) c in
      loop fuel' (S i) n a b c'
    else
      c
  end.
(* !benchmark @end code_aux *)

Definition concat (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let n := (length a + length b)%nat in
  let c := repeat 0%Z n in
  loop n O n a b c
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_lt n' f
  end.
(* !benchmark @end postcond_aux *)

Definition concat_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a + length b)%nat) &&
  (forall_nat_lt (length a) (fun k => (nth k result 0%Z =? nth k a 0%Z))) &&
  (forall_nat_lt (length b) (fun k => (nth (k + length a) result 0%Z =? nth k b 0%Z)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem concat_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    concat_precond a b = true ->
    concat_postcond a b (concat a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
