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
Require Import Coq.Arith.PeanoNat.
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
Definition maxStrength_precond_dec (nums : list Z) : bool :=
  negb (match nums with | [] => true | _ => false end).
(* !benchmark @end precond_aux *)

Definition maxStrength_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  nums <> []
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => []
  | S m => range m ++ [m]
  end.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | x :: _, 0%nat => x
  | _ :: xs, S m => nth_Z xs m
  end.

Fixpoint powerSet_helper (l : list Z) (n : nat) (i : nat) (mask : nat) : list Z :=
  match i with
  | 0%nat => []
  | S i' =>
      let rest := powerSet_helper l n i' mask in
      if Nat.eqb (Nat.land (Nat.shiftr mask i') 1%nat) 1%nat then
        (nth_Z l i') :: rest
      else
        rest
  end.

Definition powerSet (l : list Z) : list (list Z) :=
  let n := length l in
  let masks := range (Nat.pow 2%nat n) in
  map (fun mask => powerSet_helper l n n mask) masks.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => (x * product xs)%Z
  end.

Fixpoint max_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | [x] => Some x
  | x :: xs =>
      match max_list xs with
      | None => Some x
      | Some y => Some (Z.max x y)
      end
  end.

Definition filter_nonempty (l : list (list Z)) : list (list Z) :=
  filter (fun x => negb (match x with | [] => true | _ => false end)) l.
(* !benchmark @end code_aux *)

Definition maxStrength (nums : (list Z)) (h_precond : maxStrength_precond nums) : Z :=
  (* !benchmark @start code *)
  let powerSet_result := powerSet nums in
  let nonEmpty := filter_nonempty powerSet_result in
  let products := map product nonEmpty in
  match max_list products with
  | Some m => m
  | None => (-1000000)
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs =>
      let rest := sublists xs in
      rest ++ map (cons x) rest
  end.

Fixpoint all {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (f x) (all f xs)
  end.

Fixpoint contains_Z (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | y :: ys => orb (Z.eqb x y) (contains_Z ys x)
  end.

Definition maxStrength_postcond_dec (nums : list Z) (result : Z) : bool :=
  let sublists_result := sublists nums in
  let nonempty_sublists := filter_nonempty sublists_result in
  let products := map product nonempty_sublists in
  andb (contains_Z products result)
       (all (fun x => (x <=? result)%Z) products).
(* !benchmark @end postcond_aux *)

Definition maxStrength_postcond (nums : (list Z)) (result : Z) (h_precond : maxStrength_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let sublists_result := sublists nums in
  let nonempty_sublists := filter_nonempty sublists_result in
  let products := map (fun subset => fold_left Z.mul subset 1) nonempty_sublists in
  In result products /\ Forall (fun x => (x <= result)%Z) products
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxStrength_postcond_satisfied (nums : (list Z)) (h_precond : maxStrength_precond nums) :
    maxStrength_postcond nums (maxStrength nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
