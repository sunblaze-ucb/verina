(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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
Fixpoint list_pairwise_le (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && list_pairwise_le tl
  end.
(* !benchmark @end precond_aux *)

Definition CanyonSearch_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat && (1 <=? length b)%nat && list_pairwise_le a && list_pairwise_le b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition nth_default_Z (l : list Z) (n : nat) (d : Z) : Z :=
  nth n l d.

Fixpoint canyonSearchAux (a : list Z) (b : list Z) (m n : nat) (d : nat) (fuel : nat) : nat :=
  match fuel with
  | O => d
  | S fuel' =>
    if (m <? length a)%nat && (n <? length b)%nat then
      let am := nth_default_Z a m 0 in
      let bn := nth_default_Z b n 0 in
      let diff := Z.abs_nat (am - bn) in
      let new_d := if (diff <? d)%nat then diff else d in
      if am <=? bn then
        canyonSearchAux a b (S m) n new_d fuel'
      else
        canyonSearchAux a b m (S n) new_d fuel'
    else
      d
  end.
(* !benchmark @end code_aux *)

Definition CanyonSearch (a : (list Z)) (b : (list Z)) : nat :=
  (* !benchmark @start code *)
  let a0 := nth_default_Z a 0 0 in
  let b0 := nth_default_Z b 0 0 in
  let init := Z.abs_nat (a0 - b0) in
  let fuel := (length a + length b)%nat in
  canyonSearchAux a b 0 0 init fuel
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition existsb_pair (f : Z -> Z -> bool) (l1 l2 : list Z) : bool :=
  existsb (fun ai => existsb (fun bi => f ai bi) l2) l1.

Definition forallb_pair (f : Z -> Z -> bool) (l1 l2 : list Z) : bool :=
  forallb (fun ai => forallb (fun bi => f ai bi) l2) l1.
(* !benchmark @end postcond_aux *)

Definition CanyonSearch_postcond (a : (list Z)) (b : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  existsb_pair (fun ai bi => (result =? Z.abs_nat (ai - bi))%nat) a b &&
  forallb_pair (fun ai bi => (result <=? Z.abs_nat (ai - bi))%nat) a b
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CanyonSearch_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    CanyonSearch_precond a b = true ->
    CanyonSearch_postcond a b (CanyonSearch a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
