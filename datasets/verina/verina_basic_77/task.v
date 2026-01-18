(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Definition modify_array_element_precond_dec (arr : list (list nat)) (index1 : nat) (index2 : nat) (val : nat) : bool :=
  (index1 <? length arr) && 
  match nth_error arr index1 with
  | Some inner => index2 <? length inner
  | None => false
  end.
(* !benchmark @end precond_aux *)

Definition modify_array_element_precond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) : Prop :=
  (* !benchmark @start precond *)
  (index1 < length arr)%nat /\
(index2 < length (nth index1 arr []))%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint update_at {A : Type} (l : list A) (idx : nat) (new_val : A) : list A :=
  match l, idx with
  | [], _ => []
  | x :: xs, 0 => new_val :: xs
  | x :: xs, S n => x :: update_at xs n new_val
  end.
(* !benchmark @end code_aux *)

Definition modify_array_element (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (h_precond : modify_array_element_precond arr index1 index2 val) : (list (list nat)) :=
  (* !benchmark @start code *)
  let inner := nth index1 arr [] in
let inner' := update_at inner index2 val in
update_at arr index1 inner'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Fixpoint forall_nat_below (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S m => f m && forall_nat_below m f
  end.

Definition list_nat_eq_dec (l1 l2 : list nat) : bool :=
  if list_eq_dec Nat.eq_dec l1 l2 then true else false.

Definition modify_array_element_postcond_dec (arr : list (list nat)) (index1 : nat) (index2 : nat) (val : nat) (result : list (list nat)) : bool :=
  forall_nat_below (length arr) (fun i =>
    if Nat.eqb i index1 then true
    else match nth_error arr i, nth_error result i with
         | Some ai, Some ri => list_nat_eq_dec ai ri
         | _, _ => false
         end) &&
  match nth_error arr index1 with
  | Some inner_arr =>
      match nth_error result index1 with
      | Some inner_result =>
          forall_nat_below (length inner_arr) (fun j =>
            if Nat.eqb j index2 then true
            else match nth_error inner_arr j, nth_error inner_result j with
                 | Some vj, Some rj => Nat.eqb vj rj
                 | _, _ => false
                 end) &&
          match nth_error inner_result index2 with
          | Some v => Nat.eqb v val
          | None => false
          end
      | None => false
      end
  | None => false
  end.
(* !benchmark @end postcond_aux *)

Definition modify_array_element_postcond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (result : (list (list nat))) (h_precond : modify_array_element_precond arr index1 index2 val) : Prop :=
  (* !benchmark @start postcond *)
  (forall i, (i < length arr)%nat -> i <> index1 -> nth i result [] = nth i arr []) /\
(forall j, (j < length (nth index1 arr []))%nat -> j <> index2 -> nth j (nth index1 result []) 0%nat = nth j (nth index1 arr []) 0%nat) /\
(nth index2 (nth index1 result []) 0%nat = val)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem modify_array_element_postcond_satisfied (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (h_precond : modify_array_element_precond arr index1 index2 val) :
    modify_array_element_postcond arr index1 index2 val (modify_array_element arr index1 index2 val h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
