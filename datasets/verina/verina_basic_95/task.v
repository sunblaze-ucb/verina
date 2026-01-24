(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition swap_precond (arr : (list Z)) (i : Z) (j : Z) : bool :=
  (* !benchmark @start precond *)
  (i >=? 0) && (j >=? 0) && (Z.to_nat i <? length arr)%nat && (Z.to_nat j <? length arr)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint set_nth {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  match l with
  | [] => []
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: set_nth t n' x
    end
  end.

Definition nth_default {A : Type} (d : A) (l : list A) (n : nat) : A :=
  nth n l d.
(* !benchmark @end code_aux *)

Definition swap (arr : (list Z)) (i : Z) (j : Z) : (list Z) :=
  (* !benchmark @start code *)
  let i_nat := Z.to_nat i in
  let j_nat := Z.to_nat j in
  let val_j := nth_default 0 arr j_nat in
  let val_i := nth_default 0 arr i_nat in
  let arr1 := set_nth arr i_nat val_j in
  let arr2 := set_nth arr1 j_nat val_i in
  arr2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_default_Z (d : Z) (l : list Z) (n : nat) : Z :=
  nth n l d.

Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_lt n' f
  end.
(* !benchmark @end postcond_aux *)

Definition swap_postcond (arr : (list Z)) (i : Z) (j : Z) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  let i_nat := Z.to_nat i in
  let j_nat := Z.to_nat j in
  (nth_default_Z 0 result i_nat =? nth_default_Z 0 arr j_nat) &&
  (nth_default_Z 0 result j_nat =? nth_default_Z 0 arr i_nat) &&
  forall_nat_lt (length arr) (fun k =>
    implb ((negb (k =? i_nat)%nat) && (negb (k =? j_nat)%nat))
          (nth_default_Z 0 result k =? nth_default_Z 0 arr k))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem swap_postcond_satisfied (arr : (list Z)) (i : Z) (j : Z) :
    swap_precond arr i j = true ->
    swap_postcond arr i j (swap arr i j) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
