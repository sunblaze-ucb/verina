(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListDec.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to check if element is in list *)
Fixpoint contains_Z (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if Z.eqb h x then true else contains_Z x t
  end.

(* Remove duplicates from list *)
Fixpoint remove_dups (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if contains_Z h t then remove_dups t else h :: remove_dups t
  end.

(* Insert into sorted position *)
Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if (x <=? h)%Z then x :: l else h :: insert_sorted x t
  end.

(* Merge sort *)
Fixpoint merge_sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => fold_right insert_sorted [] l
  end.

(* Extract sublist from start to end (exclusive) *)
Fixpoint extract (l : list Z) (start len : nat) : list Z :=
  match start, l with
  | O, _ => firstn len l
  | S n, [] => []
  | S n, h :: t => extract t n len
  end.

(* Check if list is consecutive *)
Fixpoint is_consecutive_helper (l : list Z) (expected : Z) : bool :=
  match l with
  | [] => true
  | h :: t => if Z.eqb h expected then is_consecutive_helper t (expected + 1) else false
  end.

Definition is_consecutive (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => is_consecutive_helper t (h + 1)
  end.

(* Generate range from 0 to n-1 *)
Fixpoint range_nat (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range_nat n' ++ [n']
  end.

(* Flat map for lists *)
Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | h :: t => f h ++ flat_map f t
  end.

(* Maximum of two natural numbers *)
Definition nat_max (a b : nat) : nat :=
  if (a <? b)%nat then b else a.

(* Find maximum in list of nat *)
Fixpoint list_max (l : list nat) : nat :=
  match l with
  | [] => O
  | [x] => x
  | h :: t => nat_max h (list_max t)
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint NoDup_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => negb (contains_Z h t) && NoDup_dec t
  end.

Definition longestConsecutive_precond_dec (nums : list Z) : bool :=
  NoDup_dec nums.
(* !benchmark @end precond_aux *)

Definition longestConsecutive_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  NoDup nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to compute longest consecutive starting from each element *)
Fixpoint longest_from (nums_set : list Z) (x : Z) (acc : nat) : nat :=
  match acc with
  | O => O
  | S n => if contains_Z (x + 1) nums_set 
           then longest_from nums_set (x + 1) n
           else 1%nat
  end.

Fixpoint longest_consecutive_iter (nums : list Z) (nums_set : list Z) (fuel : nat) : nat :=
  match fuel, nums with
  | O, _ => O
  | _, [] => O
  | S f, x :: xs => 
      if negb (contains_Z (x - 1) nums_set) then
        let curr_len := 
          let fix count_consecutive (curr : Z) (remaining : nat) : nat :=
            match remaining with
            | O => O
            | S n => if contains_Z (curr + 1) nums_set 
                     then S (count_consecutive (curr + 1) n)
                     else 1%nat
            end
          in count_consecutive x (length nums_set)
        in
        nat_max curr_len (longest_consecutive_iter xs nums_set f)
      else
        longest_consecutive_iter xs nums_set f
  end.
(* !benchmark @end code_aux *)

Definition longestConsecutive (nums : (list Z)) (h_precond : longestConsecutive_precond nums) : nat :=
  (* !benchmark @start code *)
  match nums with
| [] => O
| _ => longest_consecutive_iter nums nums (length nums)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Generate all consecutive sublists and their lengths *)
Definition all_consecutive_lengths (nums : list Z) : list nat :=
  let sorted := merge_sort nums in
  let n := length nums in
  flat_map (fun start =>
    map (fun len => 
      let sub := extract sorted start len in
      if is_consecutive sub then length sub else O
    ) (range_nat (n - start + 1)%nat)
  ) (range_nat (n + 1)%nat).

Definition longestConsecutive_postcond_dec (nums : list Z) (result : nat) : bool :=
  match nums with
  | [] => Nat.eqb result O
  | _ => 
      let lens := all_consecutive_lengths nums in
      let max_len := list_max lens in
      Nat.eqb result max_len
  end.
(* !benchmark @end postcond_aux *)

Definition longestConsecutive_postcond (nums : (list Z)) (result : nat) (h_precond : longestConsecutive_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (nums = [] -> result = O) /\
(nums <> [] -> 
  let sorted_nums := merge_sort nums in
  let consec_lengths := 
    flat_map (fun start =>
      map (fun len => 
        let sub := extract sorted_nums start len in
        if is_consecutive sub then length sub else O
      ) (range_nat (length nums - start + 1)%nat)
    ) (range_nat (length nums + 1)%nat)
  in
  In result consec_lengths /\
  forall x, In x consec_lengths -> (x <= result)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestConsecutive_postcond_satisfied (nums : (list Z)) (h_precond : longestConsecutive_precond nums) :
    longestConsecutive_postcond nums (longestConsecutive nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
