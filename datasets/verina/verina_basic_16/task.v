(* !benchmark @start import type=task *)
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition replaceChars_precond (s : string) (oldChar : ascii) (newChar : ascii) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint replaceChars_list (cs : list ascii) (oldChar : ascii) (newChar : ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: rest =>
    let c' := if Ascii.eqb c oldChar then newChar else c in
    c' :: replaceChars_list rest oldChar newChar
  end.

Definition list_ascii_of_string (s : string) : list ascii :=
  list_ascii_of_string s.

Definition string_of_list_ascii (l : list ascii) : string :=
  string_of_list_ascii l.
(* !benchmark @end code_aux *)

Definition replaceChars (s : string) (oldChar : ascii) (newChar : ascii) : string :=
  (* !benchmark @start code *)
  let cs := list_ascii_of_string s in
  let cs' := replaceChars_list cs oldChar newChar in
  string_of_list_ascii cs'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition ascii_eqb (a b : ascii) : bool := Ascii.eqb a b.

Fixpoint nth_ascii (n : nat) (l : list ascii) (default : ascii) : ascii :=
  match l with
  | [] => default
  | x :: xs => if (n =? O)%nat then x else nth_ascii (n - 1)%nat xs default
  end.

Definition default_ascii : ascii := "000"%char.

Fixpoint check_all_indices (cs cs' : list ascii) (oldChar newChar : ascii) (i : nat) (len : nat) : bool :=
  match len with
  | O => true
  | S len' =>
    let ci := nth_ascii i cs default_ascii in
    let ci' := nth_ascii i cs' default_ascii in
    let check_old := implb (ascii_eqb ci oldChar) (ascii_eqb ci' newChar) in
    let check_other := implb (negb (ascii_eqb ci oldChar)) (ascii_eqb ci' ci) in
    check_old && check_other && check_all_indices cs cs' oldChar newChar (S i) len'
  end.
(* !benchmark @end postcond_aux *)

Definition replaceChars_postcond (s : string) (oldChar : ascii) (newChar : ascii) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  let cs' := list_ascii_of_string result in
  (length cs' =? length cs)%nat && check_all_indices cs cs' oldChar newChar O (length cs)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replaceChars_postcond_satisfied (s : string) (oldChar : ascii) (newChar : ascii) :
    replaceChars_precond s oldChar newChar = true ->
    replaceChars_postcond s oldChar newChar (replaceChars s oldChar newChar) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
