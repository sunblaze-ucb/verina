(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No auxiliary type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No auxiliary solution definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition arraySum_precond_dec (a : list Z) (b : list Z) : bool :=
  Nat.eqb (length a) (length b).
(* !benchmark @end precond_aux *)

Definition arraySum_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  length a = length b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint arraySum_loop (a : list Z) (b : list Z) (c : list Z) (i : nat) (n : nat) : list Z :=
  match n with
  | O => c
  | S n' =>
    if (i <? length a)%nat then
      match nth_error a i, nth_error b i with
      | Some ai, Some bi =>
        let c' := firstn i c ++ [(ai + bi)%Z] ++ skipn (S i) c in
        arraySum_loop a b c' (S i) n'
      | _, _ => c
      end
    else c
  end.
(* !benchmark @end code_aux *)

Definition arraySum (a : (list Z)) (b : (list Z)) (h_precond : arraySum_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let n := length a in
let c := repeat 0%Z n in
arraySum_loop a b c 0%nat n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition arraySum_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  Nat.eqb (length result) (length a) &&
  (fix check (i : nat) :=
    match i with
    | O => true
    | S i' =>
      if (i' <? length a)%nat then
        match nth_error a i', nth_error b i', nth_error result i' with
        | Some ai, Some bi, Some ri =>
          (ri =? (ai + bi)%Z)%Z && check i'
        | _, _, _ => false
        end
      else check i'
    end) (length a).
(* !benchmark @end postcond_aux *)

Definition arraySum_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : arraySum_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length a) /\ (forall i : nat, (i < length a)%nat -> exists ai bi ri, nth_error a i = Some ai /\ nth_error b i = Some bi /\ nth_error result i = Some ri /\ ri = (ai + bi)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arraySum_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : arraySum_precond a b) :
    arraySum_postcond a b (arraySum a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
