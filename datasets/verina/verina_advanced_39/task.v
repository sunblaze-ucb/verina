(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxOfList_precond_dec (lst : list nat) : bool :=
  Nat.ltb 0 (length lst).
(* !benchmark @end precond_aux *)

Definition maxOfList_precond (lst : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  (length lst > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxOfList_helper (lst : list nat) : nat :=
  match lst with
  | [] => 0%nat
  | [x] => x
  | x :: xs =>
      let maxTail := maxOfList_helper xs in
      if Nat.ltb maxTail x then x else maxTail
  end.
(* !benchmark @end code_aux *)

Definition maxOfList (lst : (list nat)) (h_precond : maxOfList_precond lst) : nat :=
  (* !benchmark @start code *)
  maxOfList_helper lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint in_list (x : nat) (lst : list nat) : Prop :=
  match lst with
  | [] => False
  | y :: ys => x = y \/ in_list x ys
  end.

Fixpoint forall_list (lst : list nat) (P : nat -> Prop) : Prop :=
  match lst with
  | [] => True
  | x :: xs => P x /\ forall_list xs P
  end.

Fixpoint in_list_dec (x : nat) (lst : list nat) : bool :=
  match lst with
  | [] => false
  | y :: ys => Nat.eqb x y || in_list_dec x ys
  end.

Fixpoint forall_list_dec (lst : list nat) (P : nat -> bool) : bool :=
  match lst with
  | [] => true
  | x :: xs => P x && forall_list_dec xs P
  end.

Definition maxOfList_postcond_dec (lst : list nat) (result : nat) : bool :=
  in_list_dec result lst && forall_list_dec lst (fun x => Nat.leb x result).
(* !benchmark @end postcond_aux *)

Definition maxOfList_postcond (lst : (list nat)) (result : nat) (h_precond : maxOfList_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  in_list result lst /\ forall_list lst (fun x => (x <= result)%nat)
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
