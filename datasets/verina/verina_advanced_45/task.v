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

Definition maxSubarraySum_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint helper (lst : list Z) (curMax : Z) (globalMax : Z) : Z :=
  match lst with
  | [] => globalMax
  | x :: rest =>
    let newCurMax := Z.max x (curMax + x) in
    let newGlobal := Z.max globalMax newCurMax in
    helper rest newCurMax newGlobal
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySum (xs : (list Z)) : Z :=
  (* !benchmark @start code *)
  match xs with
  | [] => 0
  | x :: rest => helper rest x x
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint take (n : nat) (l : list Z) : list Z :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: take n' xs
            end
  end.

Fixpoint drop (n : nat) (l : list Z) : list Z :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | _ :: xs => drop n' xs
            end
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint range_from (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: range_from (S start) len'
  end.

Definition subarray_sum (xs : list Z) (start len : nat) : Z :=
  sum_list (take len (drop start xs)).

Definition all_subarray_sums (xs : list Z) : list Z :=
  flat_map (fun start =>
    map (fun len => subarray_sum xs start len) (range_from 1 (length xs - start))
  ) (range (S (length xs))).

Definition has_result_subarray (xs : list Z) (result : Z) : bool :=
  existsb (fun sum => sum =? result) (all_subarray_sums xs).

Definition is_maximum (xs : list Z) (result : Z) : bool :=
  forallb (fun sum => sum <=? result) (all_subarray_sums xs).
(* !benchmark @end postcond_aux *)

Definition maxSubarraySum_postcond (xs : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  match xs with
  | [] => (result =? 0)
  | _ => has_result_subarray xs result && is_maximum xs result
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySum_postcond_satisfied (xs : (list Z)) :
    maxSubarraySum_precond xs = true ->
    maxSubarraySum_postcond xs (maxSubarraySum xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
