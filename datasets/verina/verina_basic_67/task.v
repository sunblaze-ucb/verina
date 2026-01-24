(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Require Import Ascii.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition ascii_eqb (a b : ascii) : bool :=
  match a, b with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7, Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3 &&
    Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition IsPalindrome_precond (x : (list ascii)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPalindromeHelper (x : list ascii) (i j : nat) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if (i <? j)%nat then
      match nth_error x i, nth_error x j with
      | Some ci, Some cj =>
        if negb (ascii_eqb ci cj) then false
        else isPalindromeHelper x (i + 1)%nat (j - 1)%nat fuel'
      | _, _ => false
      end
    else true
  end.
(* !benchmark @end code_aux *)

Definition IsPalindrome (x : (list ascii)) : bool :=
  (* !benchmark @start code *)
  match x with
  | [] => true
  | _ => isPalindromeHelper x 0 (length x - 1)%nat (length x)
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ascii_zero : ascii := Ascii false false false false false false false false.

Definition nth_default_ascii (l : list ascii) (n : nat) : ascii :=
  match nth_error l n with
  | Some c => c
  | None => ascii_zero
  end.

Fixpoint check_palindrome_indices (x : list ascii) (i : nat) : bool :=
  match i with
  | O => true
  | S i' =>
    let idx := (length x - i)%nat in
    let mirror := (length x - idx - 1)%nat in
    (ascii_eqb (nth_default_ascii x idx) (nth_default_ascii x mirror)) &&
    check_palindrome_indices x i'
  end.
(* !benchmark @end postcond_aux *)

Definition IsPalindrome_postcond (x : (list ascii)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb result (check_palindrome_indices x (length x))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem IsPalindrome_postcond_satisfied (x : (list ascii)) :
    IsPalindrome_precond x = true ->
    IsPalindrome_postcond x (IsPalindrome x) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
