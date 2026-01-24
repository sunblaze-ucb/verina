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
Fixpoint count_elem (x : nat) (xs : list nat) : nat :=
  match xs with
  | [] => O
  | y :: ys => if (y =? x)%nat then S (count_elem x ys) else count_elem x ys
  end.
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (xs : (list nat)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length xs)%nat && existsb (fun x => (length xs / 2 <? count_elem x xs)%nat) xs
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findCandidate (lst : list nat) (candidate : option nat) (count : nat) : nat :=
  match lst with
  | [] =>
    match candidate with
    | Some c => c
    | None => O
    end
  | x :: xs' =>
    match candidate with
    | Some c =>
      if (x =? c)%nat then
        findCandidate xs' (Some c) (count + 1)%nat
      else if (count =? O)%nat then
        findCandidate xs' (Some x) 1%nat
      else
        findCandidate xs' (Some c) (count - 1)%nat
    | None =>
      findCandidate xs' (Some x) 1%nat
    end
  end.
(* !benchmark @end code_aux *)

Definition majorityElement (xs : (list nat)) : nat :=
  (* !benchmark @start code *)
  findCandidate xs None O
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_elem_post (x : nat) (xs : list nat) : nat :=
  match xs with
  | [] => O
  | y :: ys => if (y =? x)%nat then S (count_elem_post x ys) else count_elem_post x ys
  end.
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (xs : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (length xs / 2 <? count_elem_post result xs)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (xs : (list nat)) :
    majorityElement_precond xs = true ->
    majorityElement_postcond xs (majorityElement xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
