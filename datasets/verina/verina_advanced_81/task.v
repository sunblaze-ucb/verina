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
Fixpoint Z_mem (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (x =? h)%Z then true else Z_mem x t
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition uniqueSorted_precond (arr : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | head :: tail =>
    if (x <=? head)%Z then x :: head :: tail
    else head :: insert x tail
  end.

Fixpoint insertionSort (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | h :: t => insert h (insertionSort t)
  end.

Fixpoint removeDups_aux (remaining : list Z) (seen : list Z) (acc : list Z) : list Z :=
  match remaining with
  | [] => rev acc
  | h :: t =>
    if Z_mem h seen then removeDups_aux t seen acc
    else removeDups_aux t (h :: seen) (h :: acc)
  end.

Definition removeDups (xs : list Z) : list Z :=
  removeDups_aux xs [] [].
(* !benchmark @end code_aux *)

Definition uniqueSorted (arr : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  insertionSort (removeDups arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_occ_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (x =? h)%Z then S (count_occ_Z x t) else count_occ_Z x t
  end.

Fixpoint is_perm_unique (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => 
    match l2 with
    | [] => true
    | _ => false
    end
  | h :: t =>
    let c1 := count_occ_Z h l1 in
    let c2 := count_occ_Z h l2 in
    ((1 <=? c1)%nat && (1 <=? c2)%nat) && is_perm_unique t l2
  end.

Fixpoint all_in (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => true
  | h :: t => Z_mem h l2 && all_in t l2
  end.

Definition is_perm_after_dedup (arr result : list Z) : bool :=
  all_in result arr && all_in arr result.

Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: ((h2 :: _) as t) => (h1 <=? h2)%Z && is_sorted t
  end.

Fixpoint no_dups (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => negb (Z_mem h t) && no_dups t
  end.
(* !benchmark @end postcond_aux *)

Definition uniqueSorted_postcond (arr : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  is_perm_after_dedup arr result && is_sorted result && no_dups result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem uniqueSorted_postcond_satisfied (arr : (list Z)) :
    uniqueSorted_precond arr = true ->
    uniqueSorted_postcond arr (uniqueSorted arr) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
