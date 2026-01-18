(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper: count occurrences of an element in a list *)
Fixpoint count_occ (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Nat.eqb x n then S (count_occ n xs) else count_occ n xs
  end.

(* Helper: get all subarrays *)
Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match n, l with
  | 0%nat, _ => l
  | S n', [] => []
  | S n', _ :: xs => drop n' xs
  end.

Fixpoint take (n : nat) (l : list nat) : list nat :=
  match n, l with
  | 0%nat, _ => []
  | S n', [] => []
  | S n', x :: xs => x :: take n' xs
  end.

Fixpoint all_subarrays_of_length_aux (nums : list nat) (start len total_len : nat) (fuel : nat) : list (list nat) :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      if Nat.leb (start + len) total_len then
        (take len (drop start nums)) :: all_subarrays_of_length_aux nums (S start) len total_len fuel'
      else
        []
  end.

Definition all_subarrays_of_length (nums : list nat) (start len : nat) : list (list nat) :=
  all_subarrays_of_length_aux nums start len (length nums) (length nums).

Fixpoint all_subarrays_by_length (nums : list nat) (len : nat) : list (list nat) :=
  match len with
  | 0%nat => []
  | S len' => all_subarrays_of_length nums 0%nat (S len') ++ all_subarrays_by_length nums len'
  end.

Definition all_subarrays (nums : list nat) : list (list nat) :=
  all_subarrays_by_length nums (length nums).

(* Helper: check if all elements in a list satisfy a predicate *)
Fixpoint all_elements (l : list nat) (p : nat -> bool) : bool :=
  match l with
  | [] => true
  | x :: xs => if p x then all_elements xs p else false
  end.

(* Helper: check if an array is good (all frequencies <= k) *)
Definition is_good_array (arr : list nat) (k : nat) : bool :=
  all_elements arr (fun x => Nat.leb (count_occ x arr) k).

(* Helper: filter lists by predicate *)
Fixpoint filter_lists (pred : list nat -> bool) (ll : list (list nat)) : list (list nat) :=
  match ll with
  | [] => []
  | x :: xs => if pred x then x :: filter_lists pred xs else filter_lists pred xs
  end.

(* Helper: check if any list has given length *)
Fixpoint any_length (ll : list (list nat)) (len : nat) : bool :=
  match ll with
  | [] => false
  | x :: xs => if Nat.eqb (length x) len then true else any_length xs len
  end.

(* Helper: check if all lists have length <= bound *)
Fixpoint all_length_le (ll : list (list nat)) (bound : nat) : bool :=
  match ll with
  | [] => true
  | x :: xs => if Nat.leb (length x) bound then all_length_le xs bound else false
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition longestGoodSubarray_precond_dec (nums : list nat) (k : nat) : bool :=
  Nat.ltb 0%nat k.
(* !benchmark @end precond_aux *)

Definition longestGoodSubarray_precond (nums : (list nat)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  (k > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper: update frequency map (represented as association list) *)
Fixpoint freq_insert (freq : list (nat * nat)) (key : nat) (value : nat) : list (nat * nat) :=
  match freq with
  | [] => [(key, value)]
  | (k', v') :: rest =>
      if Nat.eqb k' key then (key, value) :: rest
      else (k', v') :: freq_insert rest key value
  end.

Fixpoint freq_get (freq : list (nat * nat)) (key : nat) (default : nat) : nat :=
  match freq with
  | [] => default
  | (k', v') :: rest =>
      if Nat.eqb k' key then v' else freq_get rest key default
  end.

Fixpoint freq_erase (freq : list (nat * nat)) (key : nat) : list (nat * nat) :=
  match freq with
  | [] => []
  | (k', v') :: rest =>
      if Nat.eqb k' key then rest else (k', v') :: freq_erase rest key
  end.

Fixpoint freq_any_gt (freq : list (nat * nat)) (k : nat) : bool :=
  match freq with
  | [] => false
  | (_, v) :: rest => if Nat.ltb k v then true else freq_any_gt rest k
  end.

Fixpoint nth_default (l : list nat) (n : nat) (default : nat) : nat :=
  match l, n with
  | [], _ => default
  | x :: _, 0%nat => x
  | _ :: xs, S n' => nth_default xs n' default
  end.

Fixpoint longest_good_shrink (arr : list nat) (k : nat) (left : nat) (freq : list (nat * nat)) (fuel : nat) : nat * list (nat * nat) :=
  match fuel with
  | 0%nat => (left, freq)
  | S fuel' =>
      if freq_any_gt freq k then
        let lnum := nth_default arr left 0%nat in
        let lcount := freq_get freq lnum 0%nat in
        let freq' := if Nat.eqb lcount 1%nat then freq_erase freq lnum
                     else freq_insert freq lnum (lcount - 1) in
        longest_good_shrink arr k (S left) freq' fuel'
      else
        (left, freq)
  end.

Fixpoint longest_good_loop (arr : list nat) (k : nat) (right left maxLen : nat) (freq : list (nat * nat)) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => maxLen
  | S fuel' =>
      if Nat.ltb right (length arr) then
        let num := nth_default arr right 0%nat in
        let count := freq_get freq num 0%nat in
        let freq' := freq_insert freq num (S count) in
        let '(left', freq'') := longest_good_shrink arr k left freq' (length arr) in
        let newLen := right - left' + 1 in
        let maxLen' := if Nat.ltb maxLen newLen then newLen else maxLen in
        longest_good_loop arr k (S right) left' maxLen' freq'' fuel'
      else
        maxLen
  end.
(* !benchmark @end code_aux *)

Definition longestGoodSubarray (nums : (list nat)) (k : nat) (h_precond : longestGoodSubarray_precond nums k) : nat :=
  (* !benchmark @start code *)
  longest_good_loop nums k 0%nat 0%nat 0%nat [] (length nums * length nums)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestGoodSubarray_postcond_dec (nums : list nat) (k : nat) (result : nat) : bool :=
  let subarrays := all_subarrays nums in
  let valid_subarrays := filter_lists (fun arr => is_good_array arr k) subarrays in
  if Nat.eqb (length nums) 0%nat then
    Nat.eqb result 0%nat
  else
    andb (any_length valid_subarrays result) (all_length_le valid_subarrays result).
(* !benchmark @end postcond_aux *)

Definition longestGoodSubarray_postcond (nums : (list nat)) (k : nat) (result : nat) (h_precond : longestGoodSubarray_precond nums k) : Prop :=
  (* !benchmark @start postcond *)
  let subArrays := all_subarrays nums in
let validSubArrays := filter_lists (fun arr => is_good_array arr k) subArrays in
((nums = [] /\ result = 0%nat) \/
 (nums <> [] /\
  any_length validSubArrays result = true /\
  all_length_le validSubArrays result = true))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestGoodSubarray_postcond_satisfied (nums : (list nat)) (k : nat) (h_precond : longestGoodSubarray_precond nums k) :
    longestGoodSubarray_postcond nums k (longestGoodSubarray nums k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
