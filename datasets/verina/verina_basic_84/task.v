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

Definition replace_precond (arr : (list Z)) (k : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint replace_loop (oldArr : list Z) (k : Z) (i : nat) (acc : list Z) : list Z :=
  match oldArr with
  | [] => acc
  | h :: t =>
    if (h >? k)%Z then
      replace_loop t k (S i) (acc ++ [(-1)%Z])
    else
      replace_loop t k (S i) (acc ++ [h])
  end.
(* !benchmark @end code_aux *)

Definition replace (arr : (list Z)) (k : Z) : (list Z) :=
  (* !benchmark @start code *)
  replace_loop arr k O []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_or_default (l : list Z) (n : nat) (d : Z) : Z :=
  match l, n with
  | [], _ => d
  | h :: _, O => h
  | _ :: t, S n' => nth_or_default t n' d
  end.

Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_lt n' f
  end.
(* !benchmark @end postcond_aux *)

Definition replace_postcond (arr : (list Z)) (k : Z) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  forall_nat_lt (length arr) (fun i =>
    implb ((nth_or_default arr i 0) >? k)%Z ((nth_or_default result i 0) =? (-1))%Z)
  &&
  forall_nat_lt (length arr) (fun i =>
    implb (negb ((nth_or_default arr i 0) >? k)%Z) ((nth_or_default result i 0) =? (nth_or_default arr i 0))%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replace_postcond_satisfied (arr : (list Z)) (k : Z) :
    replace_precond arr k = true ->
    replace_postcond arr k (replace arr k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
