(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
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

Definition maxArray_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxArray_aux (a : list Z) (index : nat) (current : Z) (fuel : nat) : Z :=
  match fuel with
  | O => current
  | S fuel' =>
    if (index <? length a)%nat then
      let elem := nth index a 0%Z in
      let new_current := if (current >? elem)%Z then current else elem in
      maxArray_aux a (index + 1)%nat new_current fuel'
    else
      current
  end.
(* !benchmark @end code_aux *)

Definition maxArray (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  match a with
  | [] => 0%Z
  | h :: t => maxArray_aux a 1%nat h (length a)
  end
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
(* !benchmark @end postcond_aux *)

Definition maxArray_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  forall_nat_lt (length a) (fun k => (result >=? nth k a 0%Z)%Z) &&
  exists_nat_lt (length a) (fun k => (result =? nth k a 0%Z)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxArray_postcond_satisfied (a : (list Z)) :
    maxArray_precond a = true ->
    maxArray_postcond a (maxArray a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
