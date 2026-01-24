(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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
Fixpoint list_Z_nodup (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => negb (existsb (fun x => x =? h) t) && list_Z_nodup t
  end.
(* !benchmark @end precond_aux *)

Definition longestConsecutive_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  list_Z_nodup nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint mem_Z (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if h =? x then true else mem_Z x t
  end.

Fixpoint count_consecutive_from (x : Z) (s : list Z) (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
    if mem_Z (x + 1) s then S (count_consecutive_from (x + 1) s fuel')
    else O
  end.

Fixpoint longest_aux (nums s : list Z) (fuel : nat) : nat :=
  match nums with
  | [] => O
  | h :: t =>
    let rest := longest_aux t s fuel in
    if negb (mem_Z (h - 1) s) then
      let len := S (count_consecutive_from h s fuel) in
      Nat.max len rest
    else rest
  end.
(* !benchmark @end code_aux *)

Definition longestConsecutive (nums : (list Z)) : nat :=
  (* !benchmark @start code *)
  let s := nums in
  longest_aux nums s (length nums)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2) && list_Z_eqb t1 t2
  | _, _ => false
  end.

Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert_sorted x t
  end.

Fixpoint sort_Z (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_Z t)
  end.

Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n' default
  end.

Definition extract_Z (l : list Z) (start len : nat) : list Z :=
  firstn len (skipn start l).

Fixpoint seq_nat (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq_nat (S start) len'
  end.

Definition isConsecutive (seq : list Z) : bool :=
  match seq with
  | [] => true
  | h :: t =>
    let indexed := combine seq (seq_nat O (length seq)) in
    forallb (fun p => (fst p =? h + Z.of_nat (snd p))) indexed
  end.

Fixpoint seq_nat' (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq_nat' (S start) len'
  end.

Definition isConsecutive' (seq : list Z) : bool :=
  match seq with
  | [] => true
  | h :: t =>
    let indexed := combine seq (seq_nat' O (length seq)) in
    forallb (fun p => (fst p =? h + Z.of_nat (snd p))) indexed
  end.

Definition all_sublists_lens (sorted_nums : list Z) (n : nat) : list nat :=
  flat_map (fun start =>
    map (fun len => length (extract_Z sorted_nums start len))
        (seq_nat' O (n - start + 1)%nat))
    (seq_nat' O n).

Definition consec_sublist_lens (nums : list Z) : list nat :=
  let sorted_nums := sort_Z nums in
  let n := length nums in
  filter (fun l =>
    isConsecutive' (extract_Z sorted_nums 
      (hd O (filter (fun start => 
        existsb (fun len => (length (extract_Z sorted_nums start len) =? l)%nat)
          (seq_nat' O (n - start + 1)%nat)) (seq_nat' O n)))
      l))
    (all_sublists_lens sorted_nums n).

Definition all_consec_sublists (nums : list Z) : list (list Z) :=
  let sorted_nums := sort_Z nums in
  let n := length nums in
  filter isConsecutive'
    (flat_map (fun start =>
      map (fun len => extract_Z sorted_nums start len)
          (seq_nat' O (n - start + 1)%nat))
      (seq_nat' O n)).

Definition consec_lens (nums : list Z) : list nat :=
  map (fun l => length l) (all_consec_sublists nums).
(* !benchmark @end postcond_aux *)

Definition longestConsecutive_postcond (nums : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let consec_sublist_lens := consec_lens nums in
  implb (list_Z_eqb nums []) (result =? O)%nat &&
  implb (negb (list_Z_eqb nums []))
    (existsb (fun l => (l =? result)%nat) consec_sublist_lens &&
     forallb (fun l => (l <=? result)%nat) consec_sublist_lens)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestConsecutive_postcond_satisfied (nums : (list Z)) :
    longestConsecutive_precond nums = true ->
    longestConsecutive_postcond nums (longestConsecutive nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
