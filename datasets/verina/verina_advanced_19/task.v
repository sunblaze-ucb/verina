(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to compare two ascii characters *)
Definition ascii_eqb (c1 c2 : ascii) : bool :=
  match ascii_dec c1 c2 with
  | left _ => true
  | right _ => false
  end.

(* Helper function to compare two lists of ascii characters *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | c1 :: l1', c2 :: l2' => ascii_eqb c1 c2 && list_ascii_eqb l1' l2'
  | _, _ => false
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isCleanPalindrome_precond_dec (s : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isCleanPalindrome_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Check if a character is an uppercase alphabet letter *)
Definition isUpperAlpha (c : ascii) : bool :=
  (("A" <=? c) && (c <=? "Z"))%char.

(* Check if a character is a lowercase alphabet letter *)
Definition isLowerAlpha (c : ascii) : bool :=
  (("a" <=? c) && (c <=? "z"))%char.

(* Determine if a character is alphabetic *)
Definition isAlpha (c : ascii) : bool :=
  isUpperAlpha c || isLowerAlpha c.

(* Convert a single character to lowercase *)
Definition toLower (c : ascii) : ascii :=
  if isUpperAlpha c then
    ascii_of_nat (nat_of_ascii c + 32)
  else c.

(* Normalize a character: keep only lowercase letters *)
Definition normalizeChar (c : ascii) : option ascii :=
  if isAlpha c then Some (toLower c) else None.

(* Normalize a string into a list of lowercase alphabetic characters *)
Fixpoint normalizeString_list (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: cs =>
    match normalizeChar c with
    | Some c' => c' :: normalizeString_list cs
    | None => normalizeString_list cs
    end
  end.

Definition normalizeString (s : string) : list ascii :=
  normalizeString_list (list_ascii_of_string s).

(* Reverse the list *)
Definition reverseList (xs : list ascii) : list ascii :=
  rev xs.
(* !benchmark @end code_aux *)

Definition isCleanPalindrome (s : string) (h_precond : isCleanPalindrome_precond s) : bool :=
  (* !benchmark @start code *)
  let norm := normalizeString s in
  list_ascii_eqb norm (reverseList norm)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isCleanPalindrome_postcond_dec (s : string) (result : bool) : bool :=
  let norm := normalizeString s in
  if result then
    list_ascii_eqb norm (rev norm)
  else
    negb (list_ascii_eqb norm (rev norm)).
(* !benchmark @end postcond_aux *)

Definition isCleanPalindrome_postcond (s : string) (result : bool) (h_precond : isCleanPalindrome_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let norm := normalizeString s in
  (result = true -> norm = rev norm) /\
  (result = false -> norm <> rev norm)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isCleanPalindrome_postcond_satisfied (s : string) (h_precond : isCleanPalindrome_precond s) :
    isCleanPalindrome_postcond s (isCleanPalindrome s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
