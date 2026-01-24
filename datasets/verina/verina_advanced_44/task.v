(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition maxSubarraySumDivisibleByK_precond (arr : (list Z)) (k : Z) : bool :=
  (* !benchmark @start precond *)
  (k >? 0)%Z
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint computePrefixSums (arr : list Z) (acc : Z) : list Z :=
  match arr with
  | [] => [acc]
  | h :: t => acc :: computePrefixSums t (acc + h)
  end.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n'
  end.

Fixpoint minList (arr : list Z) (default : Z) : Z :=
  match arr with
  | [] => default
  | [h] => h
  | h :: t => Z.min h (minList t h)
  end.

Fixpoint maxSumForLen (prefixSums : list Z) (len : nat) (start : nat) (maxStarts : nat) (currentMax : Z) : Z :=
  match maxStarts with
  | O => currentMax
  | S maxStarts' =>
    let endIdx := (start + len)%nat in
    let subarraySum := (nth_Z prefixSums endIdx) - (nth_Z prefixSums start) in
    let newMax := Z.max currentMax subarraySum in
    maxSumForLen prefixSums len (S start) maxStarts' newMax
  end.

Fixpoint iterateLengths (prefixSums : list Z) (n : nat) (k : Z) (len : nat) (currentMax : Z) : Z :=
  match len with
  | O => currentMax
  | S len' =>
    let actualLen := (n - len')%nat in
    let newMax :=
      if ((Z.of_nat actualLen) mod k =? 0) && (1 <=? actualLen)%nat then
        let numStarts := (n - actualLen + 1)%nat in
        maxSumForLen prefixSums actualLen O numStarts currentMax
      else
        currentMax
    in
    iterateLengths prefixSums n k len' newMax
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySumDivisibleByK (arr : (list Z)) (k : Z) : Z :=
  (* !benchmark @start code *)
  let n := length arr in
    match n with
    | O => 0
    | _ =>
      if (k =? 0) then 0
      else
        let prefixSums := computePrefixSums arr 0 in
        let minElem := minList arr 0 in
        let default := minElem - 1 in
        let maxSum := iterateLengths prefixSums n k (S n) default in
        if (maxSum =? default) then 0 else maxSum
    end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sublist (arr : list Z) (start len : nat) : list Z :=
  match start, arr with
  | O, _ => firstn len arr
  | S start', [] => []
  | S start', _ :: t => sublist t start' len
  end.

Fixpoint sumList (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sumList t
  end.

Fixpoint allSubarraysFromStart (arr : list Z) (start : nat) (len : nat) : list (list Z) :=
  match len with
  | O => [[]]
  | S len' => (sublist arr start len) :: allSubarraysFromStart arr start len'
  end.

Fixpoint allSubarraysHelper (arr : list Z) (start : nat) (n : nat) : list (list Z) :=
  match start with
  | O => allSubarraysFromStart arr O (n + 1)%nat
  | S start' => allSubarraysFromStart arr (n - start)%nat (start + 1)%nat ++ allSubarraysHelper arr start' n
  end.

Definition allSubarrays (arr : list Z) : list (list Z) :=
  let n := length arr in
  allSubarraysHelper arr n n.

Definition isDivisibleByK (subarray : list Z) (k : Z) : bool :=
  let len := length subarray in
  ((Z.of_nat len) mod k =? 0) && (1 <=? len)%nat.

Definition divisibleSubarrays (arr : list Z) (k : Z) : list (list Z) :=
  filter (fun sub => isDivisibleByK sub k) (allSubarrays arr).

Definition subarraySums (arr : list Z) (k : Z) : list Z :=
  map sumList (divisibleSubarrays arr k).

Fixpoint maxInList (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | [h] => h
  | h :: t => Z.max h (maxInList t h)
  end.
(* !benchmark @end postcond_aux *)

Definition maxSubarraySumDivisibleByK_postcond (arr : (list Z)) (k : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let sums := subarraySums arr k in
    let n := length sums in
    implb (n =? O)%nat (result =? 0) &&
    implb (1 <=? n)%nat (existsb (fun s => s =? result) sums && forallb (fun s => s <=? result) sums)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySumDivisibleByK_postcond_satisfied (arr : (list Z)) (k : Z) :
    maxSubarraySumDivisibleByK_precond arr k = true ->
    maxSubarraySumDivisibleByK_postcond arr k (maxSubarraySumDivisibleByK arr k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
