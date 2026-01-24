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

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition toUppercase_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isLowerCase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a" <=? n)%nat && (n <=? nat_of_ascii "z")%nat.

Definition shiftMinus32 (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  ascii_of_nat ((n - 32) mod 128).

Definition toUpperChar (c : ascii) : ascii :=
  if isLowerCase c then shiftMinus32 c else c.

Fixpoint mapChars (cs : list ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: rest => toUpperChar c :: mapChars rest
  end.
(* !benchmark @end code_aux *)

Definition toUppercase (s : string) : string :=
  (* !benchmark @start code *)
  let cs := list_ascii_of_string s in
  let cs' := mapChars cs in
  string_of_list_ascii cs'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isLowerCase_post (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a" <=? n)%nat && (n <=? nat_of_ascii "z")%nat.

Definition shiftMinus32_post (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  ascii_of_nat ((n - 32) mod 128).

Fixpoint nth_ascii (l : list ascii) (n : nat) : ascii :=
  match l, n with
  | [], _ => "000"%char
  | h :: _, O => h
  | _ :: t, S n' => nth_ascii t n'
  end.

Fixpoint check_all_indices (cs cs' : list ascii) (i len : nat) : bool :=
  match len with
  | O => true
  | S len' =>
    let c := nth_ascii cs i in
    let c' := nth_ascii cs' i in
    let check_lower := implb (isLowerCase_post c) (Ascii.eqb c' (shiftMinus32_post c)) in
    let check_not_lower := implb (negb (isLowerCase_post c)) (Ascii.eqb c' c) in
    check_lower && check_not_lower && check_all_indices cs cs' (S i) len'
  end.
(* !benchmark @end postcond_aux *)

Definition toUppercase_postcond (s : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  let cs' := list_ascii_of_string result in
  (length cs' =? length cs)%nat && check_all_indices cs cs' 0 (length cs)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem toUppercase_postcond_satisfied (s : string) :
    toUppercase_precond s = true ->
    toUppercase_postcond s (toUppercase s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
