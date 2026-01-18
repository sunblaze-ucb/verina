(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxSubarraySumDivisibleByK_precond_dec (arr : list Z) (k : Z) : bool :=
  (k >? 0)%Z.
(* !benchmark @end precond_aux *)

Definition maxSubarraySumDivisibleByK_precond (arr : (list Z)) (k : Z) : Prop :=
  (* !benchmark @start precond *)
  (k > 0)%Z
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint prefix_sums_helper (arr : list Z) (acc : Z) : list Z :=
  match arr with
  | [] => [acc]
  | x :: xs => acc :: prefix_sums_helper xs (acc + x)%Z
  end.

Definition prefix_sums (arr : list Z) : list Z :=
  0%Z :: prefix_sums_helper arr 0%Z.

Fixpoint list_min_helper (l : list Z) (current_min : Z) : Z :=
  match l with
  | [] => current_min
  | x :: xs => list_min_helper xs (Z.min current_min x)
  end.

Definition list_min (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: xs => list_min_helper xs x
  end.

Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: xs => (x + list_sum xs)%Z
  end.

Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match n, l with
  | O, x :: _ => x
  | S n', _ :: xs => nth_Z xs n' default
  | _, [] => default
  end.

Fixpoint range_nat (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range_nat n' ++ [n']
  end.

Fixpoint subarray_sum_at (prefixSums : list Z) (start len : nat) : Z :=
  let endIdx := (start + len)%nat in
  (nth_Z prefixSums endIdx 0%Z - nth_Z prefixSums start 0%Z)%Z.

Fixpoint max_sum_for_starts (prefixSums : list Z) (starts : list nat) (len : nat) (current_max : Z) : Z :=
  match starts with
  | [] => current_max
  | start :: rest =>
      let subsum := subarray_sum_at prefixSums start len in
      max_sum_for_starts prefixSums rest len (Z.max current_max subsum)
  end.

Fixpoint max_sum_for_lengths (prefixSums : list Z) (lengths : list nat) (n : nat) (k : Z) (current_max : Z) : Z :=
  match lengths with
  | [] => current_max
  | len :: rest =>
      if andb (Nat.eqb (len mod (Z.to_nat k))%nat 0%nat) (Nat.ltb 0%nat len) then
        let max_start := (n - len + 1)%nat in
        let starts := range_nat max_start in
        let new_max := max_sum_for_starts prefixSums starts len current_max in
        max_sum_for_lengths prefixSums rest n k new_max
      else
        max_sum_for_lengths prefixSums rest n k current_max
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySumDivisibleByK (arr : (list Z)) (k : Z) (h_precond : maxSubarraySumDivisibleByK_precond arr k) : Z :=
  (* !benchmark @start code *)
  let n := length arr in
  if orb (Nat.eqb n 0%nat) (Z.eqb k 0%Z) then 0%Z
  else
    let prefixSums := prefix_sums arr in
    let minElem := list_min arr 0%Z in
    let default := (minElem - 1)%Z in
    let lengths := range_nat (n + 1)%nat in
    let maxSum := max_sum_for_lengths prefixSums lengths n k default in
    if (maxSum =? default)%Z then 0%Z else maxSum
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint extract (l : list Z) (start len : nat) : list Z :=
  match start, l with
  | O, _ => firstn len l
  | S start', [] => []
  | S start', _ :: xs => extract xs start' len
  end.

Fixpoint all_subarrays_helper (arr : list Z) (fuel : nat) (start : nat) : list (list Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      match skipn start arr with
      | [] => []
      | _ =>
          let len := (length arr - start)%nat in
          let subarrays_from_start := map (fun l => extract arr start l) (range_nat (len + 1)%nat) in
          subarrays_from_start ++ all_subarrays_helper arr fuel' (S start)
      end
  end.

Definition all_subarrays (arr : list Z) : list (list Z) :=
  all_subarrays_helper arr (length arr) 0%nat.

Definition divisible_subarrays (arr : list Z) (k : Z) : list (list Z) :=
  filter (fun subarray => 
    andb (Nat.eqb (length subarray mod Z.to_nat k)%nat 0%nat) (Nat.ltb 0%nat (length subarray))) 
    (all_subarrays arr).

Definition subarray_sums (arr : list Z) (k : Z) : list Z :=
  map list_sum (divisible_subarrays arr k).

Fixpoint all_leq (l : list Z) (x : Z) : Prop :=
  match l with
  | [] => True
  | y :: ys => (y <= x)%Z /\ all_leq ys x
  end.

Fixpoint all_leq_dec (l : list Z) (x : Z) : bool :=
  match l with
  | [] => true
  | y :: ys => andb (Z.leb y x) (all_leq_dec ys x)
  end.

Definition maxSubarraySumDivisibleByK_postcond_dec (arr : list Z) (k : Z) (result : Z) : bool :=
  let sums := subarray_sums arr k in
  if Nat.eqb (length sums) 0%nat then
    (result =? 0)%Z
  else
    andb (existsb (fun sum => (sum =? result)%Z) sums) (all_leq_dec sums result).
(* !benchmark @end postcond_aux *)

Definition maxSubarraySumDivisibleByK_postcond (arr : (list Z)) (k : Z) (result : Z) (h_precond : maxSubarraySumDivisibleByK_precond arr k) : Prop :=
  (* !benchmark @start postcond *)
  let subarrays := all_subarrays arr in
  let divisibleSubarrays := filter (fun subarray => 
    andb (Nat.eqb (length subarray mod Z.to_nat k)%nat 0%nat) (Nat.ltb 0%nat (length subarray))) subarrays in
  let subarraySums := map list_sum divisibleSubarrays in
  ((length subarraySums = 0)%nat -> result = 0%Z) /\
  ((length subarraySums > 0)%nat -> In result subarraySums /\ all_leq subarraySums result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySumDivisibleByK_postcond_satisfied (arr : (list Z)) (k : Z) (h_precond : maxSubarraySumDivisibleByK_precond arr k) :
    maxSubarraySumDivisibleByK_postcond arr k (maxSubarraySumDivisibleByK arr k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
