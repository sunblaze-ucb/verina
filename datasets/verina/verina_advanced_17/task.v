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

Definition insertionSort_precond (l : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insertElement (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: ys =>
      if (x <=? y)%Z then
        x :: y :: ys
      else
        y :: insertElement x ys
  end.

Fixpoint sortList (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => insertElement x (sortList xs)
  end.
(* !benchmark @end code_aux *)

Definition insertionSort (l : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  sortList l
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y)%Z && is_sorted xs
    end
  end.

Fixpoint count_occ_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_occ_Z x t) else count_occ_Z x t
  end.

Fixpoint is_perm (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | h :: t => (count_occ_Z h l1 =? count_occ_Z h l2)%nat && is_perm t l2
  end.
(* !benchmark @end postcond_aux *)

Definition insertionSort_postcond (l : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  is_sorted result && is_perm l result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insertionSort_postcond_satisfied (l : (list Z)) :
    insertionSort_precond l = true ->
    insertionSort_postcond l (insertionSort l) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
