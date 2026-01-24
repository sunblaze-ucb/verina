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
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && is_sorted tl
  end.
(* !benchmark @end precond_aux *)

Definition BinarySearch_precond (a : (list Z)) (key : Z) : bool :=
  (* !benchmark @start precond *)
  is_sorted a
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default (l : list Z) (n : nat) (d : Z) : Z :=
  match l, n with
  | [], _ => d
  | x :: _, O => x
  | _ :: xs, S n' => nth_default xs n' d
  end.

Fixpoint binarySearchLoop (a : list Z) (key : Z) (lo hi : nat) (fuel : nat) : nat :=
  match fuel with
  | O => lo
  | S fuel' =>
    if (lo <? hi)%nat then
      let mid := ((lo + hi) / 2)%nat in
      let midVal := nth_default a mid 0 in
      if (midVal <? key) then
        binarySearchLoop a key (mid + 1)%nat hi fuel'
      else
        binarySearchLoop a key lo mid fuel'
    else
      lo
  end.
(* !benchmark @end code_aux *)

Definition BinarySearch (a : (list Z)) (key : Z) : nat :=
  (* !benchmark @start code *)
  binarySearchLoop a key 0%nat (length a) (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint firstn_Z (n : nat) (l : list Z) : list Z :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: xs => x :: firstn_Z n' xs
  end.

Fixpoint skipn_Z (n : nat) (l : list Z) : list Z :=
  match n, l with
  | O, l => l
  | _, [] => []
  | S n', _ :: xs => skipn_Z n' xs
  end.
(* !benchmark @end postcond_aux *)

Definition BinarySearch_postcond (a : (list Z)) (key : Z) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result <=? length a)%nat && forallb (fun x => x <? key) (firstn_Z result a) && forallb (fun x => key <=? x) (skipn_Z result a)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem BinarySearch_postcond_satisfied (a : (list Z)) (key : Z) :
    BinarySearch_precond a key = true ->
    BinarySearch_postcond a key (BinarySearch a key) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
