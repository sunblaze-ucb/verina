(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Nat.
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
Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S k => range k ++ [k]
  end.

Definition nth_Z (l : list Z) (i : nat) : Z :=
  nth i l 0.

Definition any_pair_sums_to (nums : list Z) (target : Z) : bool :=
  existsb (fun i =>
    existsb (fun j =>
      (nth_Z nums i + nth_Z nums j =? target)%Z
    ) (range i)
  ) (range (length nums)).

Definition count_pairs (nums : list Z) (target : Z) : nat :=
  length (flat_map (fun i =>
    filter (fun j =>
      (nth_Z nums i + nth_Z nums j =? target)%Z
    ) (range i)
  ) (range (length nums))).
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  (2 <=? length nums)%nat &&
  any_pair_sums_to nums target &&
  (count_pairs nums target =? 1)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition nth_Z_code (l : list Z) (i : nat) : Z :=
  nth i l 0.

Fixpoint findIndices (nums : list Z) (target : Z) (i j fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
    if (length nums <=? i)%nat then
      []
    else if (length nums <=? j)%nat then
      findIndices nums target (i + 1)%nat (i + 2)%nat fuel'
    else
      if (nth_Z_code nums i + nth_Z_code nums j =? target)%Z then
        [i; j]
      else
        findIndices nums target i (j + 1)%nat fuel'
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) : (list nat) :=
  (* !benchmark @start code *)
  findIndices nums target 0%nat 1%nat (length nums * length nums)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_nat (l : list nat) (i : nat) : nat :=
  nth i l 0%nat.

Definition nth_Z_post (l : list Z) (i : nat) : Z :=
  nth i l 0.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (list nat)) : bool :=
  (* !benchmark @start postcond *)
  (length result =? 2)%nat &&
  (nth_nat result 0 <? length nums)%nat &&
  (nth_nat result 1 <? length nums)%nat &&
  (nth_nat result 0 <? nth_nat result 1)%nat &&
  (nth_Z_post nums (nth_nat result 0) + nth_Z_post nums (nth_nat result 1) =? target)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) :
    twoSum_precond nums target = true ->
    twoSum_postcond nums target (twoSum nums target) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
