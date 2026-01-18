(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl => Nat.leb x y && is_sorted_nat tl
  end.

Definition smallestMissingNumber_precond_dec (s : list nat) : bool :=
  is_sorted_nat s.
(* !benchmark @end precond_aux *)

Definition smallestMissingNumber_precond (s : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  match s with
| [] => True
| x :: xs => 
  (fix pairwise_le (l : list nat) (prev : nat) : Prop :=
    match l with
    | [] => True
    | y :: ys => prev <= y /\ pairwise_le ys y
    end) xs x
end
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findMissing (v : nat) (l : list nat) : nat :=
  match l with
  | [] => v
  | x :: xs =>
    if Nat.ltb v x then v
    else if Nat.eqb x v then findMissing (v + 1) xs
    else findMissing v xs
  end.
(* !benchmark @end code_aux *)

Definition smallestMissingNumber (s : (list nat)) (h_precond : smallestMissingNumber_precond s) : nat :=
  (* !benchmark @start code *)
  findMissing 0%nat s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_mem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => Nat.eqb x n || list_mem_nat n xs
  end.

Fixpoint all_less_in_list (k : nat) (result : nat) (s : list nat) : bool :=
  match k with
  | 0 => if Nat.eqb result 0 then true else list_mem_nat 0 s
  | S k' => if Nat.ltb (S k') result then (list_mem_nat (S k') s && all_less_in_list k' result s) else true
  end.

Definition smallestMissingNumber_postcond_dec (s : list nat) (result : nat) : bool :=
  negb (list_mem_nat result s) && 
  (fix check_all (k : nat) :=
    match k with
    | 0 => true
    | S k' => if Nat.ltb k' result then (list_mem_nat k' s && check_all k') else true
    end) result.
(* !benchmark @end postcond_aux *)

Definition smallestMissingNumber_postcond (s : (list nat)) (result : nat) (h_precond : smallestMissingNumber_precond s) : Prop :=
  (* !benchmark @start postcond *)
  ~ In result s /\ (forall k : nat, k < result -> In k s)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem smallestMissingNumber_postcond_satisfied (s : (list nat)) (h_precond : smallestMissingNumber_precond s) :
    smallestMissingNumber_postcond s (smallestMissingNumber s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
