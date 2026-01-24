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

Definition longestIncreasingSubsequence_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint binary_search_left (sub : list Z) (num : Z) (left right : nat) (fuel : nat) : nat :=
  match fuel with
  | O => left
  | S fuel' =>
    if (left <? right)%nat then
      let mid := ((left + right) / 2)%nat in
      match nth_error sub mid with
      | None => left
      | Some v =>
        if (v =? num)%Z then
          binary_search_left sub num left mid fuel'
        else if (v <? num)%Z then
          binary_search_left sub num (S mid) right fuel'
        else
          binary_search_left sub num left mid fuel'
      end
    else left
  end.

Fixpoint set_nth (l : list Z) (idx : nat) (val : Z) : list Z :=
  match l, idx with
  | [], _ => []
  | _ :: t, O => val :: t
  | h :: t, S n => h :: set_nth t n val
  end.

Definition last_default (l : list Z) (d : Z) : Z :=
  match l with
  | [] => d
  | _ => last l d
  end.

Fixpoint lis_loop (nums : list Z) (sub : list Z) : list Z :=
  match nums with
  | [] => sub
  | num :: rest =>
    let len := length sub in
    if (last_default sub (num - 1) <? num)%Z then
      lis_loop rest (sub ++ [num])
    else
      let pos := binary_search_left sub num O (len - 1)%nat len in
      lis_loop rest (set_nth sub pos num)
    end.

Definition longestIncreasingSubsequence_impl (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t =>
    let final_sub := lis_loop t [h] in
    Z.of_nat (length final_sub)
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  longestIncreasingSubsequence_impl nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_subsequences_aux (nums : list Z) : list (list Z) :=
  match nums with
  | [] => [[]]
  | x :: xs =>
    let subs := all_subsequences_aux xs in
    subs ++ map (fun sub => x :: sub) subs
  end.

Definition all_subsequences (nums : list Z) : list (list Z) :=
  all_subsequences_aux nums.

Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) => (x <? y)%Z && is_strictly_increasing rest
  end.

Definition increasing_subseq_lengths (nums : list Z) : list nat :=
  map (fun l => length l) (filter is_strictly_increasing (all_subsequences nums)).

Definition list_contains_nat (l : list nat) (n : nat) : bool :=
  existsb (fun x => (x =? n)%nat) l.

Definition list_all_le_nat (l : list nat) (n : nat) : bool :=
  forallb (fun x => (x <=? n)%nat) l.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let lens := increasing_subseq_lengths nums in
  let result_nat := Z.to_nat result in
  list_contains_nat lens result_nat && list_all_le_nat lens result_nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (nums : (list Z)) :
    longestIncreasingSubsequence_precond nums = true ->
    longestIncreasingSubsequence_postcond nums (longestIncreasingSubsequence nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
