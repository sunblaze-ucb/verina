(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition replace_precond_dec (arr : list Z) (k : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition replace_precond (arr : (list Z)) (k : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint replace_loop (oldArr : list Z) (k : Z) (i : nat) (acc : list Z) : list Z :=
  match i with
  | O => acc
  | S i' =>
    let idx := (length oldArr - i)%nat in
    if (idx <? length oldArr)%nat then
      match nth_error oldArr idx with
      | Some elem =>
        if (elem >? k)%Z then
          replace_loop oldArr k i' (firstn idx acc ++ [-1] ++ skipn (idx + 1)%nat acc)
        else
          replace_loop oldArr k i' acc
      | None => replace_loop oldArr k i' acc
      end
    else
      acc
  end.

Fixpoint replace_loop_iter (oldArr : list Z) (k : Z) (i : nat) (acc : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (i <? length oldArr)%nat then
      match nth_error oldArr i with
      | Some elem =>
        if (elem >? k)%Z then
          replace_loop_iter oldArr k (i + 1)%nat (firstn i acc ++ [-1] ++ skipn (i + 1)%nat acc) fuel'
        else
          replace_loop_iter oldArr k (i + 1)%nat acc fuel'
      | None => acc
      end
    else
      acc
  end.
(* !benchmark @end code_aux *)

Definition replace (arr : (list Z)) (k : Z) (h_precond : replace_precond arr k) : (list Z) :=
  (* !benchmark @start code *)
  replace_loop_iter arr k 0%nat arr (length arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition replace_postcond_dec (arr : list Z) (k : Z) (result : list Z) : bool :=
  let len := length arr in
  if (length result =? len)%nat then
    forallb (fun i =>
      match nth_error arr i, nth_error result i with
      | Some ai, Some ri =>
        if (ai >? k)%Z then (ri =? (-1))%Z
        else (ri =? ai)%Z
      | _, _ => false
      end
    ) (seq 0 len)
  else false.
(* !benchmark @end postcond_aux *)

Definition replace_postcond (arr : (list Z)) (k : Z) (result : (list Z)) (h_precond : replace_precond arr k) : Prop :=
  (* !benchmark @start postcond *)
  (forall i : nat, (i < length arr)%nat ->
  match nth_error arr i with
  | Some ai => (ai > k)%Z -> 
    match nth_error result i with
    | Some ri => ri = (-1)%Z
    | None => False
    end
  | None => False
  end) /\
(forall i : nat, (i < length arr)%nat ->
  match nth_error arr i with
  | Some ai => (ai <= k)%Z -> 
    match nth_error result i with
    | Some ri => ri = ai
    | None => False
    end
  | None => False
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replace_postcond_satisfied (arr : (list Z)) (k : Z) (h_precond : replace_precond arr k) :
    replace_postcond arr k (replace arr k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
