(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution helpers *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition concat_precond_dec (a : list Z) (b : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition concat_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint concat_loop (i : nat) (n : nat) (a : list Z) (b : list Z) (c : list Z) (size_a : nat) : list Z :=
  match n with
  | O => c
  | S n' =>
    let value := if (i <? size_a)%nat then
                   nth i a 0
                 else
                   nth (i - size_a)%nat b 0
    in
    concat_loop (S i) n' a b (app (firstn i c) (value :: skipn (S i) c)) size_a
  end.
(* !benchmark @end code_aux *)

Definition concat (a : (list Z)) (b : (list Z)) (h_precond : concat_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let n := ((length a) + (length b))%nat in
let c := repeat 0 n in
concat_loop 0%nat n a b c (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition concat_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  let size_a := length a in
  let size_b := length b in
  let size_result := length result in
  andb (Nat.eqb size_result (size_a + size_b)%nat)
    (andb (forallb (fun k => Z.eqb (nth k result 0) (nth k a 0)) (seq 0 size_a))
          (forallb (fun k => Z.eqb (nth k result 0) (nth k b 0)) (seq 0 size_b))).
(* !benchmark @end postcond_aux *)

Definition concat_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : concat_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (length result = (length a) + (length b))%nat /\
(forall k, (k < length a)%nat -> nth k result 0 = nth k a 0) /\
(forall k, (k < length b)%nat -> nth (k + length a)%nat result 0 = nth k b 0)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem concat_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : concat_precond a b) :
    concat_postcond a b (concat a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
