(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxOfList_precond_dec (lst : list nat) : bool :=
  negb (match lst with
        | [] => true
        | _ => false
        end).
(* !benchmark @end precond_aux *)

Definition maxOfList_precond (lst : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  lst <> []
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxOfList_helper (lst : list nat) : nat :=
  match lst with
  | [] => 0%nat
  | [x] => x
  | x :: xs =>
      let maxTail := maxOfList_helper xs in
      if (maxTail <? x)%nat then x else maxTail
  end.
(* !benchmark @end code_aux *)

Definition maxOfList (lst : (list nat)) (h_precond : maxOfList_precond lst) : nat :=
  (* !benchmark @start code *)
  maxOfList_helper lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint elem_of_nat (x : nat) (lst : list nat) : Prop :=
  match lst with
  | [] => False
  | y :: ys => x = y \/ elem_of_nat x ys
  end.

Fixpoint elem_of_nat_dec (x : nat) (lst : list nat) : bool :=
  match lst with
  | [] => false
  | y :: ys => Nat.eqb x y || elem_of_nat_dec x ys
  end.

Fixpoint all_le (lst : list nat) (bound : nat) : Prop :=
  match lst with
  | [] => True
  | x :: xs => x <= bound /\ all_le xs bound
  end.

Fixpoint all_le_dec (lst : list nat) (bound : nat) : bool :=
  match lst with
  | [] => true
  | x :: xs => (x <=? bound)%nat && all_le_dec xs bound
  end.

Definition maxOfList_postcond_dec (lst : list nat) (result : nat) : bool :=
  elem_of_nat_dec result lst && all_le_dec lst result.
(* !benchmark @end postcond_aux *)

Definition maxOfList_postcond (lst : (list nat)) (result : nat) (h_precond : maxOfList_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  elem_of_nat result lst /\ all_le lst result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxOfList_postcond_satisfied (lst : (list nat)) (h_precond : maxOfList_precond lst) :
    maxOfList_postcond lst (maxOfList lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
