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

Definition reverse_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint reverse_core (arr : list Z) (i : nat) (fuel : nat) : list Z :=
  match fuel with
  | O => arr
  | S fuel' =>
    if (i <? length arr / 2)%nat then
      let j := (length arr - 1 - i)%nat in
      let vi := nth i arr 0%Z in
      let vj := nth j arr 0%Z in
      let arr' := firstn i arr ++ [vj] ++ skipn (i + 1) arr in
      let arr'' := firstn j arr' ++ [vi] ++ skipn (j + 1) arr' in
      reverse_core arr'' (i + 1)%nat fuel'
    else
      arr
  end.
(* !benchmark @end code_aux *)

Definition reverse (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  reverse_core a O (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint check_all_indices (result a : list Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    let i := n' in
    let expected_idx := (length a - 1 - i)%nat in
    (nth i result 0%Z =? nth expected_idx a 0%Z) && check_all_indices result a n'
  end.
(* !benchmark @end postcond_aux *)

Definition reverse_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  (length result =? length a)%nat && check_all_indices result a (length a)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverse_postcond_satisfied (a : (list Z)) :
    reverse_precond a = true ->
    reverse_postcond a (reverse a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
