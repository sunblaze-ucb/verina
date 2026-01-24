(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_pairwise_lt (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <? y)%nat && list_pairwise_lt tl
  end.
(* !benchmark @end precond_aux *)

Definition smallestMissing_precond (l : (list nat)) : bool :=
  (* !benchmark @start precond *)
  list_pairwise_lt l
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint search (lst : list nat) (n : nat) : nat :=
  match lst with
  | [] => n
  | x :: xs =>
    if (x =? n)%nat then
      search xs (n + 1)%nat
    else if (n <? x)%nat then
      n
    else
      search xs n
  end.
(* !benchmark @end code_aux *)

Definition smallestMissing (l : (list nat)) : nat :=
  (* !benchmark @start code *)
  search l 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nat_in_list (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => (x =? n)%nat || nat_in_list n xs
  end.

Fixpoint all_less_in_list (result : nat) (l : list nat) : bool :=
  match result with
  | O => true
  | S r' => nat_in_list r' l && all_less_in_list r' l
  end.
(* !benchmark @end postcond_aux *)

Definition smallestMissing_postcond (l : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  negb (nat_in_list result l) && all_less_in_list result l
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem smallestMissing_postcond_satisfied (l : (list nat)) :
    smallestMissing_precond l = true ->
    smallestMissing_postcond l (smallestMissing l) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
