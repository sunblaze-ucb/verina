(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition lengthOfLIS_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxInList (l : list nat) : nat :=
  match l with
  | [] => O
  | [x] => x
  | x :: xs => let m := maxInList xs in if (m <=? x)%nat then x else m
  end.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint nth_nat (l : list nat) (n : nat) : nat :=
  match l, n with
  | [], _ => O
  | x :: _, O => x
  | _ :: xs, S n' => nth_nat xs n'
  end.

Fixpoint update_list (l : list nat) (idx : nat) (v : nat) : list nat :=
  match l, idx with
  | [], _ => []
  | _ :: xs, O => v :: xs
  | x :: xs, S n' => x :: update_list xs n' v
  end.

Fixpoint inner_loop (nums : list Z) (dp : list nat) (i : nat) (j : nat) : list nat :=
  match j with
  | O => dp
  | S j' =>
    let curr_j := (i - j)%nat in
    let new_dp :=
      if ((nth_Z nums curr_j <? nth_Z nums i)%Z && 
          (nth_nat dp i <? nth_nat dp curr_j + 1)%nat)
      then update_list dp i (nth_nat dp curr_j + 1)%nat
      else dp
    in inner_loop nums new_dp i j'
  end.

Fixpoint outer_loop (nums : list Z) (dp : list nat) (i : nat) (n : nat) : list nat :=
  match n with
  | O => dp
  | S n' =>
    let new_dp := inner_loop nums dp i i in
    outer_loop nums new_dp (S i) n'
  end.

Definition lengthOfLIS_aux (nums : list Z) : nat :=
  match nums with
  | [] => O
  | _ =>
    let n := length nums in
    let dp := repeat 1%nat n in
    let final_dp := outer_loop nums dp 1%nat (n - 1)%nat in
    maxInList final_dp
  end.
(* !benchmark @end code_aux *)

Definition lengthOfLIS (nums : (list Z)) : nat :=
  (* !benchmark @start code *)
  lengthOfLIS_aux nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint subsequences {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => let subs := subsequences xs in subs ++ map (fun sub => x :: sub) subs
  end.

Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => ((x <? y)%Z && is_strictly_increasing rest)
  end.

Definition all_subseq (nums : list Z) : list (list Z) :=
  subsequences nums.

Definition increasing_subseq_lens (nums : list Z) : list nat :=
  map (@length Z) (filter is_strictly_increasing (all_subseq nums)).

Fixpoint list_contains_nat (l : list nat) (n : nat) : bool :=
  match l with
  | [] => false
  | x :: xs => if (x =? n)%nat then true else list_contains_nat xs n
  end.
(* !benchmark @end postcond_aux *)

Definition lengthOfLIS_postcond (nums : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let lens := increasing_subseq_lens nums in
  list_contains_nat lens result && forallb (fun x => (x <=? result)%nat) lens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lengthOfLIS_postcond_satisfied (nums : (list Z)) :
    lengthOfLIS_precond nums = true ->
    lengthOfLIS_postcond nums (lengthOfLIS nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
