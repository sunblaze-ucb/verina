(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition nthUglyNumber_precond_dec (n : nat) : bool :=
  (n >? 0)%nat.
(* !benchmark @end precond_aux *)

Definition nthUglyNumber_precond (n : nat) : Prop :=
  (* !benchmark @start precond *)
  (n > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint divideOut (fuel n p : nat) : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
    if (andb (p >? 1)%nat (andb (n >? 0)%nat (Nat.eqb (n mod p) 0))) then
      divideOut fuel' (n / p) p
    else n
  end.

Definition isUgly (x : nat) : bool :=
  if Nat.eqb x 0 then
    false
  else
    let n1 := divideOut x x 2 in
    let n2 := divideOut n1 n1 3 in
    let n3 := divideOut n2 n2 5 in
    Nat.eqb n3 1.

Definition nextUgly (seq : list nat) (c2 c3 c5 : nat) : (nat * nat * nat * nat) :=
  let i2 := (nth c2 seq 1) * 2 in
  let i3 := (nth c3 seq 1) * 3 in
  let i5 := (nth c5 seq 1) * 5 in
  let next := min i2 (min i3 i5) in
  let c2' := if Nat.eqb next i2 then c2 + 1 else c2 in
  let c3' := if Nat.eqb next i3 then c3 + 1 else c3 in
  let c5' := if Nat.eqb next i5 then c5 + 1 else c5 in
  (next, c2', c3', c5').

Fixpoint loop (i : nat) (seq : list nat) (c2 c3 c5 : nat) : list nat :=
  match i with
  | 0 => seq
  | S i' =>
    let '(next, c2', c3', c5') := nextUgly seq c2 c3 c5 in
    loop i' (seq ++ [next]) c2' c3' c5'
  end.
(* !benchmark @end code_aux *)

Definition nthUglyNumber (n : nat) (h_precond : nthUglyNumber_precond n) : nat :=
  (* !benchmark @start code *)
  let result_list := loop (n - 1) [1%nat] 0%nat 0%nat 0%nat in
  nth (n - 1) result_list 1%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nthUglyNumber_postcond_dec (n : nat) (result : nat) : bool :=
  let ugly_numbers := filter isUgly (seq 0 result) in
  andb (isUgly result) (Nat.eqb (length ugly_numbers) (n - 1)%nat).
(* !benchmark @end postcond_aux *)

Definition nthUglyNumber_postcond (n : nat) (result : nat) (h_precond : nthUglyNumber_precond n) : Prop :=
  (* !benchmark @start postcond *)
  isUgly result = true /\
  (length (filter (fun i => isUgly i) (seq 0 result)) = n - 1)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem nthUglyNumber_postcond_satisfied (n : nat) (h_precond : nthUglyNumber_precond n) :
    nthUglyNumber_postcond n (nthUglyNumber n h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
