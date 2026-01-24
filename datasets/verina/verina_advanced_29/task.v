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
Fixpoint count_nat (x : nat) (l : list nat) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%nat then S (count_nat x t) else count_nat x t
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition longestGoodSubarray_precond (nums : (list nat)) (k : nat) : bool :=
  (* !benchmark @start precond *)
  (0 <? k)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint all_freq_le_k (window : list nat) (k : nat) : bool :=
  match window with
  | [] => true
  | h :: t => ((count_nat h window) <=? k)%nat && all_freq_le_k t k
  end.

Fixpoint shrink_window_left (window : list nat) (k : nat) : list nat :=
  match window with
  | [] => []
  | h :: t => if all_freq_le_k window k then window else shrink_window_left t k
  end.

Fixpoint longestGoodSubarray_loop (nums_suffix : list nat) (window : list nat) (k : nat) (maxLen : nat) : nat :=
  match nums_suffix with
  | [] => maxLen
  | h :: t =>
    let new_window := window ++ [h] in
    let shrunk := shrink_window_left new_window k in
    let new_max := max maxLen (length shrunk) in
    longestGoodSubarray_loop t shrunk k new_max
  end.
(* !benchmark @end code_aux *)

Definition longestGoodSubarray (nums : (list nat)) (k : nat) : nat :=
  (* !benchmark @start code *)
  longestGoodSubarray_loop nums [] k O
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Fixpoint take (n : nat) (l : list nat) : list nat :=
  match n, l with
  | O, _ => []
  | S n', [] => []
  | S n', h :: t => h :: take n' t
  end.

Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match n, l with
  | O, l' => l'
  | S n', [] => []
  | S n', _ :: t => drop n' t
  end.

Definition subarray (nums : list nat) (start len : nat) : list nat :=
  take len (drop start nums).

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition all_subarrays (nums : list nat) : list (list nat) :=
  flat_map (fun start =>
    map (fun len => subarray nums start len) (range (length nums - start + 1))
  ) (range (length nums + 1)).

Definition is_good_subarray (arr : list nat) (k : nat) : bool :=
  forallb (fun x => (count_nat x arr <=? k)%nat) arr.

Definition valid_subarrays (nums : list nat) (k : nat) : list (list nat) :=
  filter (fun arr => is_good_subarray arr k) (all_subarrays nums).

Definition max_length_in (arrs : list (list nat)) : nat :=
  fold_left (fun acc arr => max acc (length arr)) arrs O.
(* !benchmark @end postcond_aux *)

Definition longestGoodSubarray_postcond (nums : (list nat)) (k : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  match nums with
  | [] => (result =? 0)%nat
  | _ =>
    let valids := valid_subarrays nums k in
    existsb (fun arr => (length arr =? result)%nat) valids &&
    forallb (fun arr => (length arr <=? result)%nat) valids
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestGoodSubarray_postcond_satisfied (nums : (list nat)) (k : nat) :
    longestGoodSubarray_precond nums k = true ->
    longestGoodSubarray_postcond nums k (longestGoodSubarray nums k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
