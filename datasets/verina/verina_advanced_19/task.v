(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition isCleanPalindrome_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isUpperAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.leb (nat_of_ascii "A") n && Nat.leb n (nat_of_ascii "Z").

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.leb (nat_of_ascii "a") n && Nat.leb n (nat_of_ascii "z").

Definition isAlpha (c : ascii) : bool :=
  isUpperAlpha c || isLowerAlpha c.

Definition toLower (c : ascii) : ascii :=
  if isUpperAlpha c then ascii_of_nat ((nat_of_ascii c) + 32) else c.

Definition normalizeChar (c : ascii) : option ascii :=
  if isAlpha c then Some (toLower c) else None.

Fixpoint normalizeString (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: rest =>
    match normalizeChar c with
    | Some c' => c' :: normalizeString rest
    | None => normalizeString rest
    end
  end.

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => Nat.eqb (nat_of_ascii h1) (nat_of_ascii h2) && list_ascii_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end code_aux *)

Definition isCleanPalindrome (s : string) : bool :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string s in
  let norm := normalizeString chars in
  list_ascii_eqb norm (rev norm)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isUpperAlpha_post (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.leb (nat_of_ascii "A") n && Nat.leb n (nat_of_ascii "Z").

Definition isLowerAlpha_post (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.leb (nat_of_ascii "a") n && Nat.leb n (nat_of_ascii "z").

Definition isAlpha_post (c : ascii) : bool :=
  isUpperAlpha_post c || isLowerAlpha_post c.

Definition toLower_post (c : ascii) : ascii :=
  if isUpperAlpha_post c then ascii_of_nat ((nat_of_ascii c) + 32) else c.

Definition normalizeChar_post (c : ascii) : option ascii :=
  if isAlpha_post c then Some (toLower_post c) else None.

Fixpoint normalizeString_post (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: rest =>
    match normalizeChar_post c with
    | Some c' => c' :: normalizeString_post rest
    | None => normalizeString_post rest
    end
  end.

Fixpoint list_ascii_eqb_post (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => Nat.eqb (nat_of_ascii h1) (nat_of_ascii h2) && list_ascii_eqb_post t1 t2
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition isCleanPalindrome_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let chars := list_ascii_of_string s in
  let norm := normalizeString_post chars in
  let isPalin := list_ascii_eqb_post norm (rev norm) in
  implb result isPalin && implb (negb result) (negb isPalin)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isCleanPalindrome_postcond_satisfied (s : string) :
    isCleanPalindrome_precond s = true ->
    isCleanPalindrome_postcond s (isCleanPalindrome s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
