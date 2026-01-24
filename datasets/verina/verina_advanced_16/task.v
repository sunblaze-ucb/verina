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

Definition insertionSort_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (ys : list Z) : list Z :=
  match ys with
  | [] => [x]
  | y :: ys' =>
    if (x <=? y)%Z then
      x :: y :: ys'
    else
      y :: insert x ys'
  end.

Fixpoint sort (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | x :: xs => insert x (sort xs)
  end.
(* !benchmark @end code_aux *)

Definition insertionSort (xs : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  sort xs
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint pairwise_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y)%Z && pairwise_sorted tl
  end.

Fixpoint count_occ_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_occ_Z t x) else count_occ_Z t x
  end.

Fixpoint is_perm (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | h :: t => 
    (count_occ_Z l1 h =? count_occ_Z l2 h)%nat && is_perm t l2
  end.

Definition isPerm (l1 l2 : list Z) : bool :=
  (length l1 =? length l2)%nat && 
  forallb (fun x => (count_occ_Z l1 x =? count_occ_Z l2 x)%nat) l1 &&
  forallb (fun x => (count_occ_Z l1 x =? count_occ_Z l2 x)%nat) l2.
(* !benchmark @end postcond_aux *)

Definition insertionSort_postcond (xs : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  pairwise_sorted result && isPerm xs result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insertionSort_postcond_satisfied (xs : (list Z)) :
    insertionSort_precond xs = true ->
    insertionSort_postcond xs (insertionSort xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
