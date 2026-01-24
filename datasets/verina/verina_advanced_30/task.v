(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition longestIncreasingStreak_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
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

Definition longestIncreasingStreak (nums : (list Z)) : nat :=
  (* !benchmark @start code *)
  longestIncreasingStreak_aux nums None 0%nat 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition nth_Z (l : list Z) (i : nat) (default : Z) : Z :=
  nth i l default.

Definition check_increasing_pairs (nums : list Z) (start : nat) (len : nat) : bool :=
  forallb (fun i => (nth_Z nums (start + i)%nat 0 <? nth_Z nums (start + i + 1)%nat 0)%Z)
          (range (len - 1)%nat).

Definition check_not_extend_left (nums : list Z) (start : nat) : bool :=
  orb ((start =? 0)%nat) ((nth_Z nums (start - 1)%nat 0 >=? nth_Z nums start 0)%Z).

Definition check_not_extend_right (nums : list Z) (start : nat) (len : nat) : bool :=
  orb (((start + len)%nat =? length nums)%nat)
      ((nth_Z nums (start + len - 1)%nat 0 >=? nth_Z nums (start + len)%nat 0)%Z).

Definition check_streak_at (nums : list Z) (start : nat) (len : nat) : bool :=
  andb (((start + len)%nat <=? length nums)%nat)
       (andb (check_increasing_pairs nums start len)
             (andb (check_not_extend_left nums start)
                   (check_not_extend_right nums start len))).

Definition exists_streak_of_length (nums : list Z) (result : nat) : bool :=
  existsb (fun start => check_streak_at nums start result) 
          (range ((length nums - result + 1)%nat)).

Definition no_longer_streak (nums : list Z) (result : nat) : bool :=
  forallb (fun start =>
    existsb (fun i =>
      orb ((length nums <=? (start + i + 1))%nat)
          ((nth_Z nums (start + i)%nat 0 >=? nth_Z nums (start + i + 1)%nat 0)%Z)
    ) (range result)
  ) (range (length nums - result)%nat).

Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => andb (h1 =? h2)%Z (list_Z_eqb t1 t2)
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingStreak_postcond (nums : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  andb (implb (list_Z_eqb nums []) (result =? 0)%nat)
       (andb (implb (1 <=? result)%nat (exists_streak_of_length nums result))
             (no_longer_streak nums result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingStreak_postcond_satisfied (nums : (list Z)) :
    longestIncreasingStreak_precond nums = true ->
    longestIncreasingStreak_postcond nums (longestIncreasingStreak nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
