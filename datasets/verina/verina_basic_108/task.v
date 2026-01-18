(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition below_zero_precond_dec (operations : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition below_zero_precond (operations : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint buildS_helper (operations : list Z) (acc : list Z) (last : Z) : list Z :=
  match operations with
  | [] => rev acc
  | op :: ops => buildS_helper ops ((last + op)%Z :: acc) (last + op)%Z
  end.

Definition buildS (operations : list Z) : list Z :=
  0 :: buildS_helper operations [] 0.

Fixpoint check_negative (lst : list Z) : bool :=
  match lst with
  | [] => false
  | x :: xs => if (x <? 0)%Z then true else check_negative xs
  end.
(* !benchmark @end code_aux *)

Definition below_zero (operations : (list Z)) (h_precond : below_zero_precond operations) : (list Z * bool) :=
  (* !benchmark @start code *)
  let s := buildS operations in
  let result := check_negative (tl s) in
  (s, result)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : option Z :=
  match n, l with
  | 0%nat, x :: _ => Some x
  | S n', _ :: l' => nth_Z l' n'
  | _, [] => None
  end.

Fixpoint nth_Z_default (l : list Z) (n : nat) (default : Z) : Z :=
  match nth_Z l n with
  | Some v => v
  | None => default
  end.

Fixpoint forallb_range (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0%nat => true
  | S n' => forallb_range n' f && f n'
  end.

Fixpoint existsb_range (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0%nat => false
  | S n' => existsb_range n' f || f n'
  end.

Definition below_zero_postcond_dec (operations : list Z) (result : list Z * bool) : bool :=
  let s := fst result in
  let res := snd result in
  let len_check := Nat.eqb (length s) (length operations + 1)%nat in
  let first_check := match nth_Z s 0%nat with
                     | Some v => (v =? 0)%Z
                     | None => false
                     end in
  let range_check := 
    if (Nat.ltb 0%nat (length s)) then
      forallb_range (length s - 1)%nat (fun i =>
        match nth_Z s (i + 1)%nat, nth_Z s i, nth_Z operations i with
        | Some si1, Some si, Some opi => (si1 =? si + opi)%Z
        | _, _, _ => false
        end)
    else true in
  let result_true_check :=
    if res then
      existsb_range (length operations) (fun i =>
        match nth_Z s (i + 1)%nat with
        | Some v => (v <? 0)%Z
        | None => false
        end)
    else true in
  let result_false_check :=
    if negb res then
      forallb (fun x => (x >=? 0)%Z) s
    else true in
  len_check && first_check && range_check && result_true_check && result_false_check.
(* !benchmark @end postcond_aux *)

Definition below_zero_postcond (operations : (list Z)) (result : (list Z * bool)) (h_precond : below_zero_precond operations) : Prop :=
  (* !benchmark @start postcond *)
  let s := fst result in
  let res := snd result in
  length s = (length operations + 1)%nat /\
  nth_Z s 0%nat = Some 0 /\
  (forall i, (i < length s - 1)%nat ->
    exists si si1 opi,
      nth_Z s i = Some si /\
      nth_Z s (i + 1)%nat = Some si1 /\
      nth_Z operations i = Some opi /\
      si1 = (si + opi)%Z) /\
  (res = true -> exists i, (i < length operations)%nat /\
    exists v, nth_Z s (i + 1)%nat = Some v /\ (v < 0)%Z) /\
  (res = false -> forall x, In x s -> (x >= 0)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem below_zero_postcond_satisfied (operations : (list Z)) (h_precond : below_zero_precond operations) :
    below_zero_postcond operations (below_zero operations h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
