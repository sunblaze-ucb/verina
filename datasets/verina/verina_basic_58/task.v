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

Definition double_array_elements_precond (s : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint double_array_elements_aux (s_old s : list Z) (i : nat) (fuel : nat) : list Z :=
  match fuel with
  | O => s
  | S fuel' =>
    if (i <? length s)%nat then
      let old_val := nth i s_old 0%Z in
      let new_s := firstn i s ++ [2 * old_val] ++ skipn (S i) s in
      double_array_elements_aux s_old new_s (S i) fuel'
    else
      s
  end.
(* !benchmark @end code_aux *)

Definition double_array_elements (s : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  double_array_elements_aux s s 0%nat (length s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forall_index_check (result s : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' =>
    let idx := (length s - i)%nat in
    if (idx <? length s)%nat then
      let res_val := nth idx result 0%Z in
      let s_val := nth idx s 0%Z in
      (res_val =? 2 * s_val)%Z && forall_index_check result s i'
    else
      forall_index_check result s i'
  end.
(* !benchmark @end postcond_aux *)

Definition double_array_elements_postcond (s : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  (length result =? length s)%nat && forall_index_check result s (length s)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem double_array_elements_postcond_satisfied (s : (list Z)) :
    double_array_elements_precond s = true ->
    double_array_elements_postcond s (double_array_elements s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
