(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y)%nat && is_sorted xs
    end
  end.
(* !benchmark @end precond_aux *)

Definition smallestMissingNumber_precond (s : (list nat)) : bool :=
  (* !benchmark @start precond *)
  is_sorted s
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findMissing (v : nat) (l : list nat) : nat :=
  match l with
  | [] => v
  | x :: xs =>
    if (v <? x)%nat then v
    else if (x =? v)%nat then findMissing (v + 1)%nat xs
    else findMissing v xs
  end.
(* !benchmark @end code_aux *)

Definition smallestMissingNumber (s : (list nat)) : nat :=
  (* !benchmark @start code *)
  findMissing 0 s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint elem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => (n =? x)%nat || elem_nat n xs
  end.

Fixpoint all_less_than_present (k : nat) (l : list nat) : bool :=
  match k with
  | O => true
  | S k' => elem_nat k' l && all_less_than_present k' l
  end.
(* !benchmark @end postcond_aux *)

Definition smallestMissingNumber_postcond (s : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  negb (elem_nat result s) && all_less_than_present result s
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem smallestMissingNumber_postcond_satisfied (s : (list nat)) :
    smallestMissingNumber_precond s = true ->
    smallestMissingNumber_postcond s (smallestMissingNumber s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
