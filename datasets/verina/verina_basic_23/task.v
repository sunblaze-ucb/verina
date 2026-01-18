(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition differenceMinMax_precond_dec (a : list Z) : bool :=
  match length a with
  | O => false
  | S _ => true
  end.
(* !benchmark @end precond_aux *)

Definition differenceMinMax_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint differenceMinMax_loop (a : list Z) (i : nat) (minVal maxVal : Z) (fuel : nat) : Z :=
  match fuel with
  | O => maxVal - minVal
  | S fuel' =>
      if (i <? length a)%nat then
        match nth_error a i with
        | Some x =>
            let newMin := if (x <? minVal) then x else minVal in
            let newMax := if (x >? maxVal) then x else maxVal in
            differenceMinMax_loop a (i + 1)%nat newMin newMax fuel'
        | None => maxVal - minVal
        end
      else
        maxVal - minVal
  end.
(* !benchmark @end code_aux *)

Definition differenceMinMax (a : (list Z)) (h_precond : differenceMinMax_precond a) : Z :=
  (* !benchmark @start code *)
  match a with
| [] => 0
| hd :: _ =>
    differenceMinMax_loop a 1%nat hd hd (length a)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_foldl_min (acc : Z) (l : list Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => list_foldl_min (if (x <? acc) then x else acc) xs
  end.

Fixpoint list_foldl_max (acc : Z) (l : list Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => list_foldl_max (if (x >? acc) then x else acc) xs
  end.

Definition differenceMinMax_postcond_dec (a : list Z) (result : Z) : bool :=
  match a with
  | [] => true
  | hd :: tl =>
      let min_val := list_foldl_min hd tl in
      let max_val := list_foldl_max hd tl in
      (result + min_val =? max_val)
  end.
(* !benchmark @end postcond_aux *)

Definition differenceMinMax_postcond (a : (list Z)) (result : Z) (h_precond : differenceMinMax_precond a) : Prop :=
  (* !benchmark @start postcond *)
  match a with
| [] => True
| hd :: tl =>
    let min_val := list_foldl_min hd tl in
    let max_val := list_foldl_max hd tl in
    result + min_val = max_val
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem differenceMinMax_postcond_satisfied (a : (list Z)) (h_precond : differenceMinMax_precond a) :
    differenceMinMax_postcond a (differenceMinMax a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
