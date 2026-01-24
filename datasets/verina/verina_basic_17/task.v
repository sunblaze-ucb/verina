(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition isUpperCase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n)%nat && (n <=? 90)%nat.

Definition shift32 (c : ascii) : ascii :=
  ascii_of_nat ((nat_of_ascii c) + 32)%nat.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition toLowercase_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition toLower (c : ascii) : ascii :=
  if isUpperCase c then shift32 c else c.

Fixpoint mapChars (cs : list ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: rest => toLower c :: mapChars rest
  end.
(* !benchmark @end code_aux *)

Definition toLowercase (s : string) : string :=
  (* !benchmark @start code *)
  let cs := list_ascii_of_string s in
  let cs' := mapChars cs in
  string_of_list_ascii cs'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ascii_eqb (a b : ascii) : bool :=
  (nat_of_ascii a =? nat_of_ascii b)%nat.

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => ascii_eqb h1 h2 && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Definition nth_ascii (l : list ascii) (i : nat) (default : ascii) : ascii :=
  nth i l default.

Fixpoint checkAllIndices (cs cs' : list ascii) (i len : nat) : bool :=
  match len with
  | O => true
  | S len' =>
    let c := nth_ascii cs i "000"%char in
    let c' := nth_ascii cs' i "000"%char in
    let check := 
      (implb (isUpperCase c) (ascii_eqb c' (shift32 c))) &&
      (implb (negb (isUpperCase c)) (ascii_eqb c' c))
    in
    check && checkAllIndices cs cs' (S i) len'
  end.
(* !benchmark @end postcond_aux *)

Definition toLowercase_postcond (s : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  let cs' := list_ascii_of_string result in
  ((length cs' =? length cs)%nat) &&
  (checkAllIndices cs cs' O (length cs))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem toLowercase_postcond_satisfied (s : string) :
    toLowercase_precond s = true ->
    toLowercase_postcond s (toLowercase s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
