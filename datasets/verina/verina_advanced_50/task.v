(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint pairwise_le (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y)%nat && pairwise_le xs
    end
  end.
(* !benchmark @end precond_aux *)

Definition mergeSorted_precond (a1 : (list nat)) (a2 : (list nat)) : bool :=
  (* !benchmark @start precond *)
  pairwise_le a1 && pairwise_le a2
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint merge_aux (fuel : nat) (l1 l2 : list nat) (acc : list nat) : list nat :=
  match fuel with
  | O => acc ++ l1 ++ l2
  | S fuel' =>
    match l1, l2 with
    | [], [] => acc
    | [], y :: ys => merge_aux fuel' [] ys (acc ++ [y])
    | x :: xs, [] => merge_aux fuel' xs [] (acc ++ [x])
    | x :: xs, y :: ys =>
      if (x <=? y)%nat then
        merge_aux fuel' xs (y :: ys) (acc ++ [x])
      else
        merge_aux fuel' (x :: xs) ys (acc ++ [y])
    end
  end.
(* !benchmark @end code_aux *)

Definition mergeSorted (a1 : (list nat)) (a2 : (list nat)) : (list nat) :=
  (* !benchmark @start code *)
  merge_aux (length a1 + length a2) a1 a2 []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint pairwise_le_post (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y)%nat && pairwise_le_post xs
    end
  end.

Fixpoint count_occ_nat (n : nat) (l : list nat) : nat :=
  match l with
  | [] => O
  | x :: xs => if (x =? n)%nat then S (count_occ_nat n xs) else count_occ_nat n xs
  end.

Fixpoint is_perm_aux (l1 l2 : list nat) (check : list nat) : bool :=
  match check with
  | [] => true
  | x :: xs => ((count_occ_nat x l1) =? (count_occ_nat x l2))%nat && is_perm_aux l1 l2 xs
  end.

Definition is_perm (l1 l2 : list nat) : bool :=
  is_perm_aux l1 l2 (l1 ++ l2).
(* !benchmark @end postcond_aux *)

Definition mergeSorted_postcond (a1 : (list nat)) (a2 : (list nat)) (result : (list nat)) : bool :=
  (* !benchmark @start postcond *)
  pairwise_le_post result && is_perm result (a1 ++ a2)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeSorted_postcond_satisfied (a1 : (list nat)) (a2 : (list nat)) :
    mergeSorted_precond a1 a2 = true ->
    mergeSorted_postcond a1 a2 (mergeSorted a1 a2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
