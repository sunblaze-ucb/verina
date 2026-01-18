(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to check if a character is alphanumeric *)
Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)).

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n) && (n <=? 57).

Definition is_alnum (c : ascii) : bool :=
  is_alpha c || is_digit c.

(* Helper to convert character to lowercase *)
Definition to_lower (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (65 <=? n) && (n <=? 90) then
    ascii_of_nat (n + 32)
  else
    c.

(* Convert string to list of chars *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

(* Convert list to string *)
Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (list_to_string l')
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition palindromeIgnoreNonAlnum_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition palindromeIgnoreNonAlnum_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Get element at index from list *)
Fixpoint list_get {A : Type} (l : list A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: xs, S n' => list_get xs n'
  end.

(* Check palindrome helper *)
Fixpoint check_palindrome (cleaned : list ascii) (l r : nat) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if r <=? l then
        true
      else
        match list_get cleaned l, list_get cleaned r with
        | Some cl, Some cr =>
            if ascii_dec cl cr then
              check_palindrome cleaned (l + 1) (r - 1) fuel'
            else
              false
        | _, _ => false
        end
  end.
(* !benchmark @end code_aux *)

Definition palindromeIgnoreNonAlnum (s : string) (h_precond : palindromeIgnoreNonAlnum_precond s) : bool :=
  (* !benchmark @start code *)
  let cleaned := filter is_alnum (string_to_list s) in
let cleaned := map to_lower cleaned in
let n := length cleaned in
let start_index := 0%nat in
let end_index := if (n =? 0)%nat then 0%nat else (n - 1)%nat in
check_palindrome cleaned start_index end_index n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Postcondition helper *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | x :: xs, y :: ys => if ascii_dec x y then list_ascii_eqb xs ys else false
  end.

Definition palindromeIgnoreNonAlnum_postcond_dec (s : string) (result : bool) : bool :=
  let cleaned := filter is_alnum (string_to_list s) in
  let cleaned := map to_lower cleaned in
  let forward := cleaned in
  let backward := rev cleaned in
  if result then
    list_ascii_eqb forward backward
  else
    negb (list_ascii_eqb forward backward).
(* !benchmark @end postcond_aux *)

Definition palindromeIgnoreNonAlnum_postcond (s : string) (result : bool) (h_precond : palindromeIgnoreNonAlnum_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cleaned := filter is_alnum (string_to_list s) in
let cleaned := map to_lower cleaned in
let forward := cleaned in
let backward := rev cleaned in
if result then
  forward = backward
else
  forward <> backward
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem palindromeIgnoreNonAlnum_postcond_satisfied (s : string) (h_precond : palindromeIgnoreNonAlnum_precond s) :
    palindromeIgnoreNonAlnum_postcond s (palindromeIgnoreNonAlnum s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
