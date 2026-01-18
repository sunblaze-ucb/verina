(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Import ListNotations.
Local Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition increasingTriplet_precond_dec (nums : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition increasingTriplet_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Length check helper *)
Fixpoint lengthCheck (xs : list Z) (acc : nat) : nat :=
  match xs with
  | [] => acc
  | _ :: rest => lengthCheck rest (acc + 1%nat)
  end.

(* Main loop that searches for increasing triplet *)
Fixpoint loop (xs : list Z) (first : Z) (second : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match xs with
      | [] => false
      | x :: rest =>
          let nextFirst := if (x <=? first)%Z then x else first in
          let nextSecond := if ((x >? first)%Z && (x <=? second)%Z)%bool then x else second in
          if (x <=? first)%Z then
            loop rest nextFirst second fuel'
          else if (x <=? second)%Z then
            loop rest first nextSecond fuel'
          else
            true
      end
  end.
(* !benchmark @end code_aux *)

Definition increasingTriplet (nums : (list Z)) (h_precond : increasingTriplet_precond nums) : bool :=
  (* !benchmark @start code *)
  let len := lengthCheck nums 0%nat in
  if Nat.ltb len 3%nat then
    false
  else
    match nums with
    | [] => false
    | f :: rest1 =>
        match rest1 with
        | [] => false
        | s :: rest2 =>
            match rest2 with
            | [] => false
            | _ => loop nums f s len
            end
        end
    end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to get element at index *)
Fixpoint nth_opt {A : Type} (l : list A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: xs, S m => nth_opt xs m
  end.

(* Check if there exists an increasing triplet *)
Fixpoint exists_triplet_aux (nums : list Z) (i j k : nat) (len : nat) : Prop :=
  match len with
  | O => False
  | S len' =>
      (exists xi xj xk : Z,
        nth_opt nums i = Some xi /\
        nth_opt nums j = Some xj /\
        nth_opt nums k = Some xk /\
        (i < j)%nat /\ (j < k)%nat /\ xi < xj /\ xj < xk) \/
      exists_triplet_aux nums i j (S k) len' \/
      exists_triplet_aux nums i (S j) k len' \/
      exists_triplet_aux nums (S i) j k len'
  end.

Definition exists_increasing_triplet (nums : list Z) : Prop :=
  exists i j k : nat,
    (i < j)%nat /\ (j < k)%nat /\ (k < length nums)%nat /\
    exists xi xj xk : Z,
      nth_opt nums i = Some xi /\
      nth_opt nums j = Some xj /\
      nth_opt nums k = Some xk /\
      xi < xj /\ xj < xk.

Definition no_increasing_triplet (nums : list Z) : Prop :=
  forall i j k : nat,
    forall xi xj xk : Z,
      nth_opt nums i = Some xi ->
      nth_opt nums j = Some xj ->
      nth_opt nums k = Some xk ->
      (i >= j)%nat \/ (j >= k)%nat \/ xi >= xj \/ xj >= xk.

(* Decidable version *)
Fixpoint check_triplet_at (nums : list Z) (i j k : nat) : bool :=
  match nth_opt nums i, nth_opt nums j, nth_opt nums k with
  | Some xi, Some xj, Some xk =>
      (Nat.ltb i j && Nat.ltb j k && (xi <? xj)%Z && (xj <? xk)%Z)%bool
  | _, _, _ => false
  end.

Fixpoint exists_triplet_dec (nums : list Z) (max_iter : nat) : bool :=
  match max_iter with
  | O => false
  | S max_iter' =>
      let len := length nums in
      let fix loop_i i :=
        match i with
        | O => false
        | S i' =>
            let fix loop_j j :=
              match j with
              | O => false
              | S j' =>
                  let fix loop_k k :=
                    match k with
                    | O => false
                    | S k' =>
                        (check_triplet_at nums i' j' k' || loop_k k')%bool
                    end
                  in
                  (loop_k len || loop_j j')%bool
              end
            in
            (loop_j len || loop_i i')%bool
        end
      in
      loop_i len
  end.

Definition increasingTriplet_postcond_dec (nums : list Z) (result : bool) : bool :=
  if result then
    exists_triplet_dec nums (length nums * length nums * length nums)%nat
  else
    negb (exists_triplet_dec nums (length nums * length nums * length nums)%nat).
(* !benchmark @end postcond_aux *)

Definition increasingTriplet_postcond (nums : (list Z)) (result : bool) (h_precond : increasingTriplet_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (result = true -> exists_increasing_triplet nums) /\
(result = false -> no_increasing_triplet nums)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem increasingTriplet_postcond_satisfied (nums : (list Z)) (h_precond : increasingTriplet_precond nums) :
    increasingTriplet_postcond nums (increasingTriplet nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
