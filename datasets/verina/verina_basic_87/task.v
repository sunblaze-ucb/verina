(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition SelectionSort_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default (l : list Z) (n : nat) (d : Z) : Z :=
  match l with
  | [] => d
  | h :: t => match n with
              | O => h
              | S n' => nth_default t n' d
              end
  end.

Fixpoint set_nth (l : list Z) (n : nat) (v : Z) : list Z :=
  match l with
  | [] => []
  | h :: t => match n with
              | O => v :: t
              | S n' => h :: set_nth t n' v
              end
  end.

Definition swap (a : list Z) (i j : nat) : list Z :=
  if andb (Nat.ltb i (length a)) (andb (Nat.ltb j (length a)) (negb (Nat.eqb i j))) then
    let vi := nth_default a i 0 in
    let vj := nth_default a j 0 in
    let a' := set_nth a i vj in
    set_nth a' j vi
  else a.

Fixpoint findMinIndexInRangeAux (arr : list Z) (start curr minIdx : nat) (fuel : nat) : nat :=
  match fuel with
  | O => minIdx
  | S fuel' =>
    if (length arr <=? curr)%nat then minIdx
    else
      let currVal := nth_default arr curr 0 in
      let minVal := nth_default arr minIdx 0 in
      let newMinIdx := if (currVal <? minVal) then curr else minIdx in
      findMinIndexInRangeAux arr start (S curr) newMinIdx fuel'
  end.

Definition findMinIndexInRange (arr : list Z) (start finish : nat) : nat :=
  findMinIndexInRangeAux arr start start start (finish - start)%nat.

Fixpoint selectionSortAux (arr : list Z) (i : nat) (n : nat) (fuel : nat) : list Z :=
  match fuel with
  | O => arr
  | S fuel' =>
    if (n <=? i)%nat then arr
    else
      let minIdx := findMinIndexInRange arr i n in
      let arr' := swap arr i minIdx in
      selectionSortAux arr' (S i) n fuel'
  end.
(* !benchmark @end code_aux *)

Definition SelectionSort (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  selectionSortAux a O (length a) (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: (h2 :: t) as tl => (h1 <=? h2) && is_sorted tl
  end.

Fixpoint count_occ_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x) then S (count_occ_Z t x) else count_occ_Z t x
  end.

Fixpoint is_perm_aux (l1 l2 : list Z) (tocheck : list Z) : bool :=
  match tocheck with
  | [] => true
  | h :: t => ((count_occ_Z l1 h =? count_occ_Z l2 h)%nat) && is_perm_aux l1 l2 t
  end.

Definition is_perm (l1 l2 : list Z) : bool :=
  is_perm_aux l1 l2 (l1 ++ l2).
(* !benchmark @end postcond_aux *)

Definition SelectionSort_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  is_sorted result && is_perm a result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SelectionSort_postcond_satisfied (a : (list Z)) :
    SelectionSort_precond a = true ->
    SelectionSort_postcond a (SelectionSort a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
