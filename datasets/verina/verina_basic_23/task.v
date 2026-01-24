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

Definition differenceMinMax_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (fuel : nat) (arr : list Z) (i : nat) (minVal maxVal : Z) : Z :=
  match fuel with
  | O => maxVal - minVal
  | S fuel' =>
    if (i <? length arr)%nat then
      let x := nth i arr 0 in
      let newMin := if x <? minVal then x else minVal in
      let newMax := if x >? maxVal then x else maxVal in
      loop fuel' arr (S i) newMin newMax
    else
      maxVal - minVal
  end.
(* !benchmark @end code_aux *)

Definition differenceMinMax (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  match a with
  | [] => 0
  | h :: _ => loop (length a) a 1%nat h h
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition foldl_min (l : list Z) (init : Z) : Z :=
  fold_left (fun acc x => if x <? acc then x else acc) l init.

Definition foldl_max (l : list Z) (init : Z) : Z :=
  fold_left (fun acc x => if x >? acc then x else acc) l init.
(* !benchmark @end postcond_aux *)

Definition differenceMinMax_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  match a with
  | [] => true
  | h :: _ => (result + foldl_min a h =? foldl_max a h)
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem differenceMinMax_postcond_satisfied (a : (list Z)) :
    differenceMinMax_precond a = true ->
    differenceMinMax_postcond a (differenceMinMax a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
