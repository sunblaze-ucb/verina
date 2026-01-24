(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
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

Definition nthUglyNumber_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  (0 <? n)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default (l : list nat) (idx : nat) (default : nat) : nat :=
  match l, idx with
  | [], _ => default
  | h :: _, O => h
  | _ :: t, S i => nth_default t i default
  end.

Definition nextUgly (seq : list nat) (c2 c3 c5 : nat) : (nat * nat * nat * nat) :=
  let i2 := (nth_default seq c2 1) * 2 in
  let i3 := (nth_default seq c3 1) * 3 in
  let i5 := (nth_default seq c5 1) * 5 in
  let next := min i2 (min i3 i5) in
  let c2' := if (next =? i2)%nat then S c2 else c2 in
  let c3' := if (next =? i3)%nat then S c3 else c3 in
  let c5' := if (next =? i5)%nat then S c5 else c5 in
  (next, c2', c3', c5').

Fixpoint ugly_loop (fuel : nat) (seq : list nat) (c2 c3 c5 : nat) : list nat :=
  match fuel with
  | O => seq
  | S fuel' =>
    let '(next, c2', c3', c5') := nextUgly seq c2 c3 c5 in
    ugly_loop fuel' (seq ++ [next]) c2' c3' c5'
  end.
(* !benchmark @end code_aux *)

Definition nthUglyNumber (n : nat) : nat :=
  (* !benchmark @start code *)
  let seq := ugly_loop (n - 1) [1] 0 0 0 in
  nth_default seq (n - 1) 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint divideOut (n p : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if andb (andb (1 <? p)%nat (0 <? n)%nat) ((n mod p) =? 0)%nat then
      divideOut (n / p) p fuel'
    else n
  end.

Definition isUgly (x : nat) : bool :=
  if (x =? 0)%nat then false
  else
    let n1 := divideOut x 2 x in
    let n2 := divideOut n1 3 n1 in
    let n3 := divideOut n2 5 n2 in
    (n3 =? 1)%nat.

Fixpoint count_ugly_below (k : nat) : nat :=
  match k with
  | O => O
  | S k' => (if isUgly k' then 1 else 0) + count_ugly_below k'
  end.
(* !benchmark @end postcond_aux *)

Definition nthUglyNumber_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  andb (isUgly result) ((count_ugly_below result) =? (n - 1))%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem nthUglyNumber_postcond_satisfied (n : nat) :
    nthUglyNumber_precond n = true ->
    nthUglyNumber_postcond n (nthUglyNumber n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
