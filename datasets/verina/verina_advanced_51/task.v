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
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Helper to check if a list is sorted (pairwise ≤) *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tl => x <= y /\ is_sorted tl
  end.

Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl => (x <=? y) && is_sorted_dec tl
  end.

Definition mergeSorted_precond_dec (a : list Z) (b : list Z) : bool :=
  is_sorted_dec a && is_sorted_dec b.
(* !benchmark @end precond_aux *)

Definition mergeSorted_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  is_sorted a /\ is_sorted b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Program Fixpoint mergeSortedAux (a : list Z) (b : list Z) 
  {measure (length a + length b)%nat} : list Z :=
  match a, b with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' =>
      if (x <=? y)%Z then
        x :: mergeSortedAux xs' (y :: ys')
      else
        y :: mergeSortedAux (x :: xs') ys'
  end.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
(* !benchmark @end code_aux *)

Definition mergeSorted (a : (list Z)) (b : (list Z)) (h_precond : mergeSorted_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let merged := mergeSortedAux a b in merged
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if two lists are permutations *)
Fixpoint count_occ (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: tl => if (x =? y)%Z then S (count_occ x tl) else count_occ x tl
  end.

(* Two lists are permutations if they have the same count for every element *)
Definition is_perm (l1 l2 : list Z) : Prop :=
  forall x : Z, count_occ x l1 = count_occ x l2.

(* Decidable version - we'll need to check finite elements *)
(* For decidability, we check a bounded set of elements *)
Fixpoint all_elems (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: tl => x :: all_elems tl
  end.

Fixpoint check_perm_on (elems : list Z) (l1 l2 : list Z) : bool :=
  match elems with
  | [] => true
  | x :: tl => Nat.eqb (count_occ x l1) (count_occ x l2) && check_perm_on tl l1 l2
  end.

Definition is_perm_dec (l1 l2 : list Z) : bool :=
  let elems := all_elems (l1 ++ l2) in
  check_perm_on elems l1 l2.

Definition mergeSorted_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  is_sorted_dec result && is_perm_dec result (a ++ b).
(* !benchmark @end postcond_aux *)

Definition mergeSorted_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : mergeSorted_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  is_sorted result /\ is_perm result (a ++ b)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSorted_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : mergeSorted_precond a b) :
    mergeSorted_postcond a b (mergeSorted a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
