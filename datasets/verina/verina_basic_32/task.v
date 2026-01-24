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

Definition swapFirstAndLast_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition nth_default (l : list Z) (i : nat) : Z :=
  nth i l 0%Z.

Definition set_nth (l : list Z) (i : nat) (v : Z) : list Z :=
  firstn i l ++ [v] ++ skipn (S i) l.
(* !benchmark @end code_aux *)

Definition swapFirstAndLast (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let first := nth_default a 0%nat in
  let last := nth_default a (length a - 1)%nat in
  let a' := set_nth a 0%nat last in
  set_nth a' (length a - 1)%nat first
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_default_post (l : list Z) (i : nat) : Z :=
  nth i l 0%Z.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.
(* !benchmark @end postcond_aux *)

Definition swapFirstAndLast_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a)%nat &&
   (nth_default_post result 0%nat =? nth_default_post a (length a - 1)%nat) &&
   (nth_default_post result (length result - 1)%nat =? nth_default_post a 0%nat) &&
   forallb (fun i => (nth_default_post result (i + 1)%nat =? nth_default_post a (i + 1)%nat)) (range (length result - 2)%nat))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem swapFirstAndLast_postcond_satisfied (a : (list Z)) :
    swapFirstAndLast_precond a = true ->
    swapFirstAndLast_postcond a (swapFirstAndLast a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
