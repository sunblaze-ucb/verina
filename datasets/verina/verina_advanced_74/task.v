(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition solution_precond (nums : (list nat)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length nums)%nat && (length nums <=? 100)%nat && forallb (fun x => (1 <=? x)%nat && (x <=? 100)%nat) nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition subarray (nums : list nat) (i j : nat) : list nat :=
  firstn (j - i + 1)%nat (skipn i nums).

Fixpoint mem_nat (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%nat then true else mem_nat x t
  end.

Fixpoint distinct_elems (l : list nat) (seen : list nat) : list nat :=
  match l with
  | [] => seen
  | h :: t => if mem_nat h seen then distinct_elems t seen else distinct_elems t (h :: seen)
  end.

Definition distinctCount (l : list nat) : nat :=
  length (distinct_elems l []).

Fixpoint inner_loop (nums : list nat) (i : nat) (d : nat) (max_d : nat) (acc : nat) : nat :=
  match max_d with
  | O => acc
  | S max_d' =>
    let subarr := subarray nums i (i + d)%nat in
    let cnt := distinctCount subarr in
    inner_loop nums i (d + 1)%nat max_d' (acc + cnt * cnt)%nat
  end.

Fixpoint outer_loop (nums : list nat) (i : nat) (n : nat) (remaining : nat) (acc : nat) : nat :=
  match remaining with
  | O => acc
  | S remaining' =>
    let inner_sum := inner_loop nums i 0 (n - i)%nat 0 in
    outer_loop nums (i + 1)%nat n remaining' (acc + inner_sum)%nat
  end.
(* !benchmark @end code_aux *)

Definition solution (nums : (list nat)) : nat :=
  (* !benchmark @start code *)
  let n := length nums in outer_loop nums 0 n n 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint postcond_mem_nat (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%nat then true else postcond_mem_nat x t
  end.

Fixpoint postcond_distinct_elems (l : list nat) (seen : list nat) : list nat :=
  match l with
  | [] => seen
  | h :: t => if postcond_mem_nat h seen then postcond_distinct_elems t seen else postcond_distinct_elems t (h :: seen)
  end.

Definition postcond_distinctCount (l : list nat) : nat :=
  length (postcond_distinct_elems l []).

Definition postcond_subarray (nums : list nat) (i j : nat) : list nat :=
  firstn (j - i + 1)%nat (skipn i nums).

Fixpoint postcond_inner_loop (nums : list nat) (i : nat) (d : nat) (max_d : nat) (acc : nat) : nat :=
  match max_d with
  | O => acc
  | S max_d' =>
    let j := (i + d)%nat in
    let subarr := postcond_subarray nums i j in
    let cnt := postcond_distinctCount subarr in
    postcond_inner_loop nums i (d + 1)%nat max_d' (acc + cnt * cnt)%nat
  end.

Fixpoint postcond_outer_loop (nums : list nat) (i : nat) (n : nat) (remaining : nat) (acc : nat) : nat :=
  match remaining with
  | O => acc
  | S remaining' =>
    let inner_sum := postcond_inner_loop nums i 0 (n - i)%nat 0 in
    postcond_outer_loop nums (i + 1)%nat n remaining' (acc + inner_sum)%nat
  end.

Definition postcond_expected (nums : list nat) : nat :=
  let n := length nums in
  postcond_outer_loop nums 0 n n 0.
(* !benchmark @end postcond_aux *)

Definition solution_postcond (nums : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let n := length nums in
    implb ((1 <=? n)%nat && (n <=? 100)%nat && forallb (fun x => (1 <=? x)%nat && (x <=? 100)%nat) nums)
          ((result =? postcond_expected nums)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem solution_postcond_satisfied (nums : (list nat)) :
    solution_precond nums = true ->
    solution_postcond nums (solution nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
