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

Definition UpdateElements_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (8 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint set_nth (l : list Z) (n : nat) (v : Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
    match n with
    | O => v :: t
    | S n' => h :: set_nth t n' v
    end
  end.

Definition nth_default (l : list Z) (n : nat) (d : Z) : Z :=
  nth n l d.
(* !benchmark @end code_aux *)

Definition UpdateElements (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let a1 := set_nth a 4 ((nth_default a 4 0) + 3) in
  let a2 := set_nth a1 7 516 in
  a2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (d : Z) : Z :=
  nth n l d.

Fixpoint set_nth_Z (l : list Z) (n : nat) (v : Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
    match n with
    | O => v :: t
    | S n' => h :: set_nth_Z t n' v
    end
  end.

Fixpoint check_unchanged (result a : list Z) (i len : nat) : bool :=
  match len with
  | O => true
  | S len' =>
    if (i =? 4)%nat then check_unchanged result a (S i) len'
    else if (i =? 7)%nat then check_unchanged result a (S i) len'
    else if (i <? length a)%nat then
      ((nth_Z result i 0 =? nth_Z a i 0) && check_unchanged result a (S i) len')%bool
    else check_unchanged result a (S i) len'
  end.
(* !benchmark @end postcond_aux *)

Definition UpdateElements_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((nth_Z result 4 0 =? (nth_Z a 4 0) + 3) &&
   (nth_Z result 7 0 =? 516) &&
   check_unchanged result a 0 (length a))%bool
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem UpdateElements_postcond_satisfied (a : (list Z)) :
    UpdateElements_precond a = true ->
    UpdateElements_postcond a (UpdateElements a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
