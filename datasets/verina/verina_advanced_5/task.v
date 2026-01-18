(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint listToNat (l : list nat) : nat :=
  match l with
  | [] => 0%nat
  | d :: ds => (d + 10 * listToNat ds)%nat
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint all_digits_lt_10 (l : list nat) : bool :=
  match l with
  | [] => true
  | d :: ds => (d <? 10) && all_digits_lt_10 ds
  end.

Definition getLast (l : list nat) : option nat :=
  match rev l with
  | [] => None
  | h :: _ => Some h
  end.

Definition addTwoNumbers_precond_dec (l1 l2 : list nat) : bool :=
  ((length l1 >? 0) && (length l2 >? 0) &&
   all_digits_lt_10 l1 && all_digits_lt_10 l2 &&
   match getLast l1 with
   | None => false
   | Some d1 => (negb (Nat.eqb d1 0)) || (Nat.eqb (length l1) 1 && Nat.eqb d1 0)
   end &&
   match getLast l2 with
   | None => false
   | Some d2 => (negb (Nat.eqb d2 0)) || (Nat.eqb (length l2) 1 && Nat.eqb d2 0)
   end)%bool.
(* !benchmark @end precond_aux *)

Definition addTwoNumbers_precond (l1 : (list nat)) (l2 : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  ((length l1 > 0)%nat /\ (length l2 > 0)%nat /\
  (forall d, In d l1 -> (d < 10)%nat) /\
  (forall d, In d l2 -> (d < 10)%nat) /\
  (match getLast l1 with
   | None => False
   | Some d => d <> 0%nat \/ l1 = [0%nat]
   end) /\
  (match getLast l2 with
   | None => False
   | Some d => d <> 0%nat \/ l2 = [0%nat]
   end))
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint addAux (l1 l2 : list nat) (carry : nat) : list nat :=
  match l1, l2 with
  | [], [] =>
      if Nat.eqb carry 0 then [] else [carry]
  | h1::t1, [] =>
      let sum := (h1 + carry)%nat in
      (Nat.modulo sum 10) :: addAux t1 [] (Nat.div sum 10)
  | [], h2::t2 =>
      let sum := (h2 + carry)%nat in
      (Nat.modulo sum 10) :: addAux [] t2 (Nat.div sum 10)
  | h1::t1, h2::t2 =>
      let sum := (h1 + h2 + carry)%nat in
      (Nat.modulo sum 10) :: addAux t1 t2 (Nat.div sum 10)
  end.
(* !benchmark @end code_aux *)

Definition addTwoNumbers (l1 : (list nat)) (l2 : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) : (list nat) :=
  (* !benchmark @start code *)
  addAux l1 l2 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition addTwoNumbers_postcond_dec (l1 l2 result : list nat) : bool :=
  (Nat.eqb (listToNat result) (listToNat l1 + listToNat l2) &&
   all_digits_lt_10 result &&
   match getLast result with
   | None => false
   | Some d => (negb (Nat.eqb d 0)) ||
                ((Nat.eqb (length l1) 1) && (Nat.eqb (length l2) 1) &&
                 match l1, l2, result with
                 | [d1], [d2], [dr] => Nat.eqb d1 0 && Nat.eqb d2 0 && Nat.eqb dr 0
                 | _, _, _ => false
                 end)
   end)%bool.
(* !benchmark @end postcond_aux *)

Definition addTwoNumbers_postcond (l1 : (list nat)) (l2 : (list nat)) (result : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) : Prop :=
  (* !benchmark @start postcond *)
  (listToNat result = (listToNat l1 + listToNat l2)%nat /\
  (forall d, In d result -> (d < 10)%nat) /\
  (match getLast result with
   | None => False
   | Some d => d <> 0%nat \/ (l1 = [0%nat] /\ l2 = [0%nat] /\ result = [0%nat])
   end))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem addTwoNumbers_postcond_satisfied (l1 : (list nat)) (l2 : (list nat)) (h_precond : addTwoNumbers_precond l1 l2) :
    addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
