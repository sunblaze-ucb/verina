(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Coq.Sorting.Sorted.
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition uniqueSorted_precond_dec (arr : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition uniqueSorted_precond (arr : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | head :: tail =>
    if (x <=? head)%Z then
      x :: head :: tail
    else
      head :: insert x tail
  end.

Fixpoint insertionSort (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | h :: t =>
    let sortedTail := insertionSort t in
    insert h sortedTail
  end.

Fixpoint aux_removeDups (remaining : list Z) (seen : list Z) (acc : list Z) : list Z :=
  match remaining with
  | [] => rev acc
  | h :: t =>
    if existsb (Z.eqb h) seen then
      aux_removeDups t seen acc
    else
      aux_removeDups t (h :: seen) (h :: acc)
  end.

Definition removeDups (xs : list Z) : list Z :=
  aux_removeDups xs [] [].
(* !benchmark @end code_aux *)

Definition uniqueSorted (arr : (list Z)) (h_precond : uniqueSorted_precond arr) : (list Z) :=
  (* !benchmark @start code *)
  insertionSort (removeDups arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Permutation.

Fixpoint remove_one (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | y :: ys => if (x =? y)%Z then ys else y :: remove_one x ys
  end.

Fixpoint mem (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | y :: ys => if (x =? y)%Z then true else mem x ys
  end.

Fixpoint nodup_aux (l : list Z) (seen : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if mem x seen then nodup_aux xs seen else x :: nodup_aux xs (x :: seen)
  end.

Definition nodup (l : list Z) : list Z :=
  nodup_aux l [].

Fixpoint is_perm (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: xs => existsb (Z.eqb x) l2 && is_perm xs (remove_one x l2)
  end.

Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: (y :: _) as tl => (x <=? y)%Z && is_sorted tl
  end.

Definition uniqueSorted_postcond_dec (arr result : list Z) : bool :=
  is_perm (nodup arr) result && is_sorted result.
(* !benchmark @end postcond_aux *)

Definition uniqueSorted_postcond (arr : (list Z)) (result : (list Z)) (h_precond : uniqueSorted_precond arr) : Prop :=
  (* !benchmark @start postcond *)
  Permutation (nodup arr) result /\ StronglySorted Z.le result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem uniqueSorted_postcond_satisfied (arr : (list Z)) (h_precond : uniqueSorted_precond arr) :
    uniqueSorted_postcond arr (uniqueSorted arr h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
