(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
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

Definition allVowels_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition toLower (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (Nat.leb 65 n && Nat.leb n 90)%bool then
    ascii_of_nat (n + 32)%nat
  else
    c.

Fixpoint normalize_str (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => toLower c :: normalize_str rest
  end.

Definition ascii_eqb (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).

Fixpoint list_contains (l : list ascii) (c : ascii) : bool :=
  match l with
  | [] => false
  | h :: t => if ascii_eqb h c then true else list_contains t c
  end.

Definition vowelSet : list ascii := ["a"; "e"; "i"; "o"; "u"]%char.
(* !benchmark @end code_aux *)

Definition allVowels (s : string) : bool :=
  (* !benchmark @start code *)
  let chars := normalize_str s in
  forallb (fun v => list_contains chars v) vowelSet
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition toLower_post (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (Nat.leb 65 n && Nat.leb n 90)%bool then
    ascii_of_nat (n + 32)%nat
  else
    c.

Fixpoint normalize_str_post (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => toLower_post c :: normalize_str_post rest
  end.

Definition ascii_eqb_post (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).

Fixpoint list_contains_post (l : list ascii) (c : ascii) : bool :=
  match l with
  | [] => false
  | h :: t => if ascii_eqb_post h c then true else list_contains_post t c
  end.

Definition vowelSet_post : list ascii := ["a"; "e"; "i"; "o"; "u"]%char.
(* !benchmark @end postcond_aux *)

Definition allVowels_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let chars := normalize_str_post s in
  Bool.eqb result (forallb (fun v => list_contains_post chars v) vowelSet_post)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allVowels_postcond_satisfied (s : string) :
    allVowels_precond s = true ->
    allVowels_postcond s (allVowels s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
