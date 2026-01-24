(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_pairwise_le (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && list_pairwise_le tl
  end.
(* !benchmark @end precond_aux *)

Definition mergeSorted_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  list_pairwise_le a && list_pairwise_le b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint mergeSortedAux (xs : list Z) : list Z -> list Z :=
  match xs with
  | [] => fun ys => ys
  | x :: xs' =>
    fix inner (ys : list Z) : list Z :=
      match ys with
      | [] => x :: xs'
      | y :: ys' =>
        if (x <=? y)
        then x :: mergeSortedAux xs' (y :: ys')
        else y :: inner ys'
      end
  end.
(* !benchmark @end code_aux *)

Definition mergeSorted (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  mergeSortedAux a b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_pairwise_le_post (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && list_pairwise_le_post tl
  end.

Fixpoint count_occ_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x) then S (count_occ_Z x t) else count_occ_Z x t
  end.

Fixpoint is_perm_Z (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | h :: t => 
    (count_occ_Z h l1 =? count_occ_Z h l2)%nat && is_perm_Z t l2
  end.

Definition is_permutation (l1 l2 : list Z) : bool :=
  (length l1 =? length l2)%nat && 
  forallb (fun x => (count_occ_Z x l1 =? count_occ_Z x l2)%nat) l1 &&
  forallb (fun x => (count_occ_Z x l1 =? count_occ_Z x l2)%nat) l2.
(* !benchmark @end postcond_aux *)

Definition mergeSorted_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  list_pairwise_le_post result && is_permutation result (a ++ b)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSorted_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    mergeSorted_precond a b = true ->
    mergeSorted_postcond a b (mergeSorted a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
