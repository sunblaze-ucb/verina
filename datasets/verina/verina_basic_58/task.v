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
Definition double_array_elements_precond_dec (s : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition double_array_elements_precond (s : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint double_array_elements_aux (s_old s : list Z) (i : nat) : list Z :=
  match i with
  | O => match s with
         | [] => []
         | hd :: tl => match s_old with
                       | [] => hd :: tl
                       | hd_old :: _ => (2 * hd_old)%Z :: (double_array_elements_aux s_old tl 1%nat)
                       end
         end
  | S i' => match s with
            | [] => []
            | hd :: tl => match nth_error s_old i with
                          | Some val => hd :: (double_array_elements_aux s_old tl (S i'))
                          | None => hd :: tl
                          end
            end
  end.

Fixpoint double_list_helper (s_old : list Z) (i : nat) : list Z :=
  match s_old with
  | [] => []
  | hd :: tl => (2 * hd)%Z :: (double_list_helper tl (S i))
  end.
(* !benchmark @end code_aux *)

Definition double_array_elements (s : (list Z)) (h_precond : double_array_elements_precond s) : (list Z) :=
  (* !benchmark @start code *)
  double_list_helper s 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint check_all_helper (result s : list Z) (remaining : nat) : bool :=
  match remaining with
  | O => true
  | S n' => match result, s with
            | r :: result', sv :: s' => 
                (r =? 2 * sv)%Z && check_all_helper result' s' n'
            | _, _ => false
            end
  end.

Definition double_array_elements_postcond_dec (s : list Z) (result : list Z) : bool :=
  (Nat.eqb (length result) (length s)) &&
  (check_all_helper result s (length s)).
(* !benchmark @end postcond_aux *)

Definition double_array_elements_postcond (s : (list Z)) (result : (list Z)) (h_precond : double_array_elements_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length s) /\
(forall i : nat, (i < length s)%nat -> 
  match nth_error result i, nth_error s i with
  | Some r, Some sv => r = (2 * sv)%Z
  | _, _ => False
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem double_array_elements_postcond_satisfied (s : (list Z)) (h_precond : double_array_elements_precond s) :
    double_array_elements_postcond s (double_array_elements s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
