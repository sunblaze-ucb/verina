(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Nat.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Bool.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition longestIncreasingStreak_precond_dec (nums : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingStreak_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint longestIncreasingStreak_aux (lst : list Z) (prev : option Z) (currLen : nat) (maxLen : nat) : nat :=
  match lst with
  | [] => Nat.max currLen maxLen
  | x :: xs =>
    match prev with
    | None => longestIncreasingStreak_aux xs (Some x) 1%nat (Nat.max 1%nat maxLen)
    | Some p =>
      if (x >? p)%Z then
        longestIncreasingStreak_aux xs (Some x) (currLen + 1)%nat (Nat.max (currLen + 1)%nat maxLen)
      else
        longestIncreasingStreak_aux xs (Some x) 1%nat (Nat.max currLen maxLen)
    end
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingStreak (nums : (list Z)) (h_precond : longestIncreasingStreak_precond nums) : nat :=
  (* !benchmark @start code *)
  longestIncreasingStreak_aux nums None 0%nat 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Require Import Bool.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, 0%nat => x
  | _ :: xs, S m => nth_Z xs m
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => []
  | S m => range m ++ [m]
  end.

Fixpoint all_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => if f x then all_nat f xs else false
  end.

Fixpoint any_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => if f x then true else any_nat f xs
  end.

Definition longestIncreasingStreak_postcond_dec (nums : list Z) (result : nat) : bool :=
  (* Case 1: Empty list means result = 0 *)
  andb (match nums with [] => Nat.eqb result 0%nat | _ => true end)
  (andb (* Case 2: If result > 0, there exists a streak of exactly that length *)
  (if Nat.ltb 0%nat result then
    any_nat (fun start =>
      andb (andb (Nat.leb (start + result)%nat (length nums))
      (all_nat (fun i =>
        (nth_Z nums (start + i)%nat <? nth_Z nums (start + i + 1)%nat)%Z
      ) (range (result - 1)%nat)))
      (andb (orb (Nat.eqb start 0%nat) (nth_Z nums (start - 1)%nat >=? nth_Z nums start)%Z)
      (orb (Nat.eqb (start + result)%nat (length nums)) (nth_Z nums (start + result - 1)%nat >=? nth_Z nums (start + result)%nat)%Z))
    ) (range (length nums - result + 1)%nat)
  else true)
  (* Case 3: No streak longer than result exists *)
  (all_nat (fun start =>
    any_nat (fun i =>
      orb (Nat.leb (length nums) (start + i + 1)%nat) (nth_Z nums (start + i)%nat >=? nth_Z nums (start + i + 1)%nat)%Z
    ) (range result)
  ) (range (length nums - result)%nat))).
(* !benchmark @end postcond_aux *)

Definition longestIncreasingStreak_postcond (nums : (list Z)) (result : nat) (h_precond : longestIncreasingStreak_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (nums = [] -> result = 0%nat) /\
  ((result > 0)%nat ->
    exists start : nat,
      In start (range (length nums - result + 1)%nat) /\
      (start + result <= length nums)%nat /\
      (forall i, In i (range (result - 1)%nat) -> (nth_Z nums (start + i)%nat < nth_Z nums (start + i + 1)%nat)%Z) /\
      (start = 0%nat \/ (nth_Z nums (start - 1)%nat >= nth_Z nums start)%Z) /\
      ((start + result)%nat = length nums \/ (nth_Z nums (start + result - 1)%nat >= nth_Z nums (start + result)%nat)%Z)) /\
  (forall start : nat, In start (range (length nums - result)%nat) ->
    exists i : nat, In i (range result) /\
      ((start + i + 1 >= length nums)%nat \/ (nth_Z nums (start + i)%nat >= nth_Z nums (start + i + 1)%nat)%Z))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingStreak_postcond_satisfied (nums : (list Z)) (h_precond : longestIncreasingStreak_precond nums) :
    longestIncreasingStreak_postcond nums (longestIncreasingStreak nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
