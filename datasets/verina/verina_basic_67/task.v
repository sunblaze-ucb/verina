(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import Bool.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition IsPalindrome_precond_dec (x : list ascii) : bool := true.
(* !benchmark @end precond_aux *)

Definition IsPalindrome_precond (x : (list ascii)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPalindromeHelper (x : list ascii) (i j : nat) (fuel : nat) : bool :=
  match fuel with
  | 0%nat => true
  | S fuel' =>
      if (i <? j)%nat then
        match nth_error x i, nth_error x j with
        | Some ci, Some cj =>
            if ascii_dec ci cj then 
              isPalindromeHelper x (i + 1)%nat (j - 1)%nat fuel'
            else false
        | _, _ => false
        end
      else true
  end.
(* !benchmark @end code_aux *)

Definition IsPalindrome (x : (list ascii)) (h_precond : IsPalindrome_precond x) : bool :=
  (* !benchmark @start code *)
  let len := length x in
if Nat.eqb len 0%nat then true 
else isPalindromeHelper x 0%nat (len - 1)%nat len
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_default (A : Type) (default : A) (l : list A) (n : nat) : A :=
  match nth_error l n with
  | Some x => x
  | None => default
  end.

Definition IsPalindrome_postcond_dec (x : list ascii) (result : bool) : bool :=
  let len := length x in
  let fix check_all (i : nat) (fuel : nat) : bool :=
    match fuel with
    | 0%nat => true
    | S fuel' =>
        if (i <? len)%nat then
          let ci := nth_default ascii zero x i in
          let cj := nth_default ascii zero x (len - i - 1)%nat in
          if ascii_dec ci cj then
            check_all (i + 1)%nat fuel'
          else false
        else true
    end
  in
  if result then check_all 0%nat len else negb (check_all 0%nat len).
(* !benchmark @end postcond_aux *)

Definition IsPalindrome_postcond (x : (list ascii)) (result : bool) (h_precond : IsPalindrome_precond x) : Prop :=
  (* !benchmark @start postcond *)
  result = true <-> (forall i : nat, (i < length x)%nat -> 
  nth_default ascii zero x i = nth_default ascii zero x (length x - i - 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem IsPalindrome_postcond_satisfied (x : (list ascii)) (h_precond : IsPalindrome_precond x) :
    IsPalindrome_postcond x (IsPalindrome x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
