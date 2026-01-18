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
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution-level helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Helper to check if any pair in a list sums to target *)
Fixpoint exists_pair_sum (l : list Z) (target : Z) : Prop :=
  match l with
  | [] => False
  | x :: xs => (exists y, In y xs /\ (x + y)%Z = target) \/ exists_pair_sum xs target
  end.

Fixpoint exists_pair_sum_dec (l : list Z) (target : Z) : bool :=
  match l with
  | [] => false
  | x :: xs => 
      (existsb (fun y => (x + y =? target)%Z) xs) || exists_pair_sum_dec xs target
  end.

Definition twoSum_precond_dec (nums : list Z) (target : Z) : bool :=
  (1 <? length nums)%nat && exists_pair_sum_dec nums target.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  (length nums > 1)%nat /\ exists_pair_sum nums target
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Inner loop: searches for a matching pair starting from index j *)
Fixpoint inner (nums : list Z) (target : Z) (i j n : nat) (vi : Z) : option (nat * nat) :=
  match n with
  | O => None
  | S n' =>
      if (j <? length nums)%nat then
        match nth_error nums j with
        | Some vj =>
            if (vi + vj =? target)%Z then
              Some (i, j)
            else
              inner nums target i (j + 1) n' vi
        | None => None
        end
      else
        None
  end.

(* Outer loop: iterates through all starting indices *)
Fixpoint outer (nums : list Z) (target : Z) (i n : nat) : option (nat * nat) :=
  match n with
  | O => None
  | S n' =>
      if (i + 1 <? length nums)%nat then
        match nth_error nums i with
        | Some vi =>
            match inner nums target i (i + 1) (length nums) vi with
            | Some result => Some result
            | None => outer nums target (i + 1) n' 
            end
        | None => None
        end
      else
        None
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) : (nat  * nat) :=
  (* !benchmark @start code *)
  match outer nums target 0%nat (length nums) with
| Some result => result
| None => (0%nat, 0%nat)  (* panic case - should not happen with valid precondition *)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to get element at index with default 0 *)
Definition get_default (nums : list Z) (i : nat) : Z :=
  match nth_error nums i with
  | Some v => v
  | None => 0%Z
  end.

(* Check if all elements in a sublist satisfy a property *)
Definition all_in_range (nums : list Z) (start len : nat) (pred : Z -> bool) : bool :=
  forallb pred (firstn len (skipn start nums)).

(* Check if no pair exists in range [0, i) *)
Fixpoint no_pair_before (nums : list Z) (target : Z) (i : nat) : Prop :=
  forall i' j', (i' < i)%nat -> (j' > i')%nat -> (j' < length nums)%nat ->
    (get_default nums i' + get_default nums j' <> target)%Z.

Definition no_pair_before_dec (nums : list Z) (target : Z) (i : nat) : bool :=
  let check_idx := fix check_idx i' fuel :=
    match fuel with
    | O => true
    | S fuel' =>
        if (i' <? i)%nat then
          let vi := get_default nums i' in
          let check_j := forallb (fun j' => 
            if andb (i' <? j')%nat (j' <? length nums)%nat then
              negb ((vi + get_default nums j') =? target)%Z
            else true) (seq 0%nat (length nums)) in
          andb check_j (check_idx (i' + 1)%nat fuel')
        else true
    end in
  check_idx 0%nat i.

(* Check if j is the smallest valid partner for i *)
Definition smallest_partner (nums : list Z) (target : Z) (i j : nat) : Prop :=
  let vi := get_default nums i in
  forall j', (i < j')%nat -> (j' < j)%nat -> (vi + get_default nums j' <> target)%Z.

Definition smallest_partner_dec (nums : list Z) (target : Z) (i j : nat) : bool :=
  let vi := get_default nums i in
  forallb (fun j' => 
    if andb (i <? j')%nat (j' <? j)%nat then
      negb ((vi + get_default nums j') =? target)%Z
    else true) (seq 0%nat (length nums)).

Definition twoSum_postcond_dec (nums : list Z) (target : Z) (result : nat * nat) : bool :=
  let '(i, j) := result in
  andb (andb (andb (andb (i <? j)%nat (j <? length nums)%nat)
  ((get_default nums i + get_default nums j) =? target)%Z)
  (no_pair_before_dec nums target i))
  (smallest_partner_dec nums target i j).
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (nat  * nat)) (h_precond : twoSum_precond nums target) : Prop :=
  (* !benchmark @start postcond *)
  let '(i, j) := result in
  (i < j)%nat /\ (j < length nums)%nat /\
  (get_default nums i + get_default nums j = target)%Z /\
  no_pair_before nums target i /\
  smallest_partner nums target i j
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
