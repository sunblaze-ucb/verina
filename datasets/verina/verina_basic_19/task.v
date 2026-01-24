(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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

Definition isSorted_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isSorted_helper (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <=? y) && isSorted_helper rest
  end.
(* !benchmark @end code_aux *)

Definition isSorted (a : (list Z)) : bool :=
  (* !benchmark @start code *)
  isSorted_helper a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (i : nat) : Z :=
  match l, i with
  | [], _ => 0
  | x :: _, O => x
  | _ :: xs, S i' => nth_Z xs i'
  end.

Fixpoint check_sorted_indices (a : list Z) (len : nat) (i : nat) : bool :=
  match i with
  | O => true
  | S i' => 
    let idx := (len - 1 - i)%nat in
    (nth_Z a idx <=? nth_Z a (S idx)) && check_sorted_indices a len i'
  end.

Definition all_pairs_sorted (a : list Z) : bool :=
  match length a with
  | O => true
  | S O => true
  | S (S n) => check_sorted_indices a (length a) (S n)
  end.
(* !benchmark @end postcond_aux *)

Definition isSorted_postcond (a : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (all_pairs_sorted a) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isSorted_postcond_satisfied (a : (list Z)) :
    isSorted_precond a = true ->
    isSorted_postcond a (isSorted a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
