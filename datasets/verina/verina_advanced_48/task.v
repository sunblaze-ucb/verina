(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition mergeSort_precond (lst : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | y :: ys =>
      if (x <=? y)%Z then
        x :: sorted
      else
        y :: insert x ys
  end.

Fixpoint insertionSort (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let sortedRest := insertionSort xs in
      insert x sortedRest
  end.
(* !benchmark @end code_aux *)

Definition mergeSort (lst : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  insertionSort lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint isSorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <=? y)%Z && isSorted rest
  end.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | y :: ys => if (x =? y)%Z then S (count x ys) else count x ys
  end.

Fixpoint isPerm (l1 l2 : list Z) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: xs => (count x l1 =? count x l2)%nat && isPerm xs l2
  end.
(* !benchmark @end postcond_aux *)

Definition mergeSort_postcond (lst : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  isSorted result && isPerm lst result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSort_postcond_satisfied (lst : (list Z)) :
    mergeSort_precond lst = true ->
    mergeSort_postcond lst (mergeSort lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
