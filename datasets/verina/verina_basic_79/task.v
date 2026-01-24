(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition onlineMax_precond (a : (list Z)) (x : nat) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat && (1 <=? x)%nat && (x <? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findBest (a : list Z) (x : nat) (i : nat) (best : Z) (fuel : nat) : Z :=
  match fuel with
  | O => best
  | S fuel' =>
    if (i <? x)%nat then
      let ai := nth i a 0%Z in
      let newBest := if (ai >? best)%Z then ai else best in
      findBest a x (i + 1)%nat newBest fuel'
    else best
  end.

Fixpoint findP (a : list Z) (x : nat) (m : Z) (i : nat) (fuel : nat) : nat :=
  match fuel with
  | O => (length a - 1)%nat
  | S fuel' =>
    if (i <? length a)%nat then
      let ai := nth i a 0%Z in
      if (ai >? m)%Z then i else findP a x m (i + 1)%nat fuel'
    else (length a - 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition onlineMax (a : (list Z)) (x : nat) : (Z  * nat) :=
  (* !benchmark @start code *)
  let best := nth 0 a 0%Z in
  let m := findBest a x 1%nat best x in
  let p := findP a x m x (length a) in
  (m, p)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_lt n' f
  end.

Fixpoint exists_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => false
  | S n' => f n' || exists_nat_lt n' f
  end.

Definition forall_nat_range (lo hi : nat) (f : nat -> bool) : bool :=
  forall_nat_lt hi (fun i => implb (lo <=? i)%nat (f i)).
(* !benchmark @end postcond_aux *)

Definition onlineMax_postcond (a : (list Z)) (x : nat) (result : (Z  * nat)) : bool :=
  (* !benchmark @start postcond *)
  let '(m, p) := result in
  let sz := length a in
  (x <=? p)%nat && (p <? sz)%nat &&
  forall_nat_lt x (fun i => (nth i a 0%Z <=? m)%Z) &&
  exists_nat_lt x (fun i => (nth i a 0%Z =? m)%Z) &&
  implb (p <? sz - 1)%nat (forall_nat_lt p (fun i => (nth i a 0%Z <? nth p a 0%Z)%Z)) &&
  implb (forall_nat_range x sz (fun i => (nth i a 0%Z <=? m)%Z)) ((p =? sz - 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem onlineMax_postcond_satisfied (a : (list Z)) (x : nat) :
    onlineMax_precond a x = true ->
    onlineMax_postcond a x (onlineMax a x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
