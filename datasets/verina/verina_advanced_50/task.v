(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to check if a list is sorted *)
Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: rest) as tail => (x <=? y) && is_sorted tail
  end.

(* Helper function to check if two lists are permutations *)
Fixpoint count_occ (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Nat.eqb x n then S (count_occ n xs) else count_occ n xs
  end.

Fixpoint all_elems (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => x :: all_elems xs
  end.

Fixpoint is_perm_helper (l1 l2 : list nat) (elems : list nat) : bool :=
  match elems with
  | [] => true
  | x :: xs => Nat.eqb (count_occ x l1) (count_occ x l2) && is_perm_helper l1 l2 xs
  end.

Definition is_perm (l1 l2 : list nat) : bool :=
  (length l1 =? length l2) && is_perm_helper l1 l2 (l1 ++ l2).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Sorted predicate in Prop *)
Inductive Sorted : list nat -> Prop :=
  | Sorted_nil : Sorted []
  | Sorted_one : forall x, Sorted [x]
  | Sorted_cons : forall x y l, x <= y -> Sorted (y :: l) -> Sorted (x :: y :: l).

Definition mergeSorted_precond_dec (a1 a2 : list nat) : bool :=
  is_sorted a1 && is_sorted a2.
(* !benchmark @end precond_aux *)

Definition mergeSorted_precond (a1 : (list nat)) (a2 : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  Sorted a1 /\ Sorted a2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint mergeSorted_helper (a1 a2 : list nat) (fuel : nat) : list nat :=
  match fuel with
  | 0%nat => a1 ++ a2
  | S fuel' =>
      match a1, a2 with
      | [], _ => a2
      | _, [] => a1
      | x :: xs, y :: ys =>
          if x <=? y then
            x :: mergeSorted_helper xs a2 fuel'
          else
            y :: mergeSorted_helper a1 ys fuel'
      end
  end.
(* !benchmark @end code_aux *)

Definition mergeSorted (a1 : (list nat)) (a2 : (list nat)) (h_precond : mergeSorted_precond a1 a2) : (list nat) :=
  (* !benchmark @start code *)
  mergeSorted_helper a1 a2 (length a1 + length a2)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Permutation predicate *)
Fixpoint Permutation_count (l1 l2 : list nat) : Prop :=
  forall x, count_occ x l1 = count_occ x l2.

Definition isPerm (l1 l2 : list nat) : Prop :=
  length l1 = length l2 /\ Permutation_count l1 l2.

Definition mergeSorted_postcond_dec (a1 a2 result : list nat) : bool :=
  is_sorted result && is_perm result (a1 ++ a2).
(* !benchmark @end postcond_aux *)

Definition mergeSorted_postcond (a1 : (list nat)) (a2 : (list nat)) (result : (list nat)) (h_precond : mergeSorted_precond a1 a2) : Prop :=
  (* !benchmark @start postcond *)
  Sorted result /\ isPerm result (a1 ++ a2)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSorted_postcond_satisfied (a1 : (list nat)) (a2 : (list nat)) (h_precond : mergeSorted_precond a1 a2) :
    mergeSorted_postcond a1 a2 (mergeSorted a1 a2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
