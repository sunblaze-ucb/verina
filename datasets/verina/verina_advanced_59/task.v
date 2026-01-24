(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition ascii_eqb (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((65 <=? n)%nat && (n <=? 90)%nat) || ((97 <=? n)%nat && (n <=? 122)%nat).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition isAlnum (c : ascii) : bool :=
  isAlpha c || isDigit c.

Definition toLower (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if ((65 <=? n)%nat && (n <=? 90)%nat)
  then ascii_of_nat (n + 32)%nat
  else c.

Fixpoint filterAlnum (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t => if isAlnum h then h :: filterAlnum t else filterAlnum t
  end.

Fixpoint mapToLower (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t => toLower h :: mapToLower t
  end.

Definition cleanString (s : string) : list ascii :=
  mapToLower (filterAlnum (list_ascii_of_string s)).
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition palindromeIgnoreNonAlnum_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_ascii (l : list ascii) (n : nat) : option ascii :=
  match l, n with
  | [], _ => None
  | h :: _, O => Some h
  | _ :: t, S n' => nth_ascii t n'
  end.

Definition option_ascii_eqb (o1 o2 : option ascii) : bool :=
  match o1, o2 with
  | None, None => true
  | Some a, Some b => ascii_eqb a b
  | _, _ => false
  end.

Fixpoint checkPalindrome (cleaned : list ascii) (l r : nat) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if (r <=? l)%nat then true
    else if option_ascii_eqb (nth_ascii cleaned l) (nth_ascii cleaned r)
         then checkPalindrome cleaned (l + 1)%nat (r - 1)%nat fuel'
         else false
  end.
(* !benchmark @end code_aux *)

Definition palindromeIgnoreNonAlnum (s : string) : bool :=
  (* !benchmark @start code *)
  let cleaned := cleanString s in
  let n := length cleaned in
  let endIdx := match n with O => O | S n' => n' end in
  checkPalindrome cleaned O endIdx n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => ascii_eqb h1 h2 && list_ascii_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition palindromeIgnoreNonAlnum_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let cleaned := cleanString s in
  let forward := cleaned in
  let backward := rev cleaned in
  if result then list_ascii_eqb forward backward
  else negb (list_ascii_eqb forward backward)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem palindromeIgnoreNonAlnum_postcond_satisfied (s : string) :
    palindromeIgnoreNonAlnum_precond s = true ->
    palindromeIgnoreNonAlnum_postcond s (palindromeIgnoreNonAlnum s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
