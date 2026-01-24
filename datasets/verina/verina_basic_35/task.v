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

(* !benchmark @end precond_aux *)

Definition MoveZeroesToEnd_precond (arr : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition filter_nonzeros (l : list Z) : list Z :=
  filter (fun x => negb (x =? 0)) l.

Definition filter_zeros (l : list Z) : list Z :=
  filter (fun x => x =? 0) l.
(* !benchmark @end code_aux *)

Definition MoveZeroesToEnd (arr : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let nonZeros := filter_nonzeros arr in
  let zeros := filter_zeros arr in
  nonZeros ++ zeros
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Count occurrences of an element in a list *)
Fixpoint count_occ_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => O
  | h :: t => if h =? x then S (count_occ_Z t x) else count_occ_Z t x
  end.

(* Check if l1 is a permutation of l2 by checking counts match for all elements *)
Fixpoint all_counts_match (elems l1 l2 : list Z) : bool :=
  match elems with
  | [] => true
  | h :: t => (count_occ_Z l1 h =? count_occ_Z l2 h)%nat && all_counts_match t l1 l2
  end.

Definition isPerm_Z (l1 l2 : list Z) : bool :=
  (length l1 =? length l2)%nat && all_counts_match l1 l1 l2 && all_counts_match l2 l1 l2.

(* Find index of first occurrence of 0 in list, return length if not found *)
Fixpoint idxOf_zero (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if h =? 0 then O else S (idxOf_zero t)
  end.

(* List equality for Z *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2) && list_Z_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition MoveZeroesToEnd_postcond (arr : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  let firstResZeroIdx := idxOf_zero result in
  isPerm_Z result arr &&
  list_Z_eqb (firstn firstResZeroIdx result) (filter (fun x => negb (x =? 0)) arr) &&
  list_Z_eqb (skipn firstResZeroIdx result) (filter (fun x => x =? 0) arr)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem MoveZeroesToEnd_postcond_satisfied (arr : (list Z)) :
    MoveZeroesToEnd_precond arr = true ->
    MoveZeroesToEnd_postcond arr (MoveZeroesToEnd arr) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
