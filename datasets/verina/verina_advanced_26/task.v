(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Require Import String.
Require Import Ascii.
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

Definition letterCombinations_precond (digits : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition digitToLetters (c : ascii) : list ascii :=
  if Nat.eqb (nat_of_ascii c) (nat_of_ascii "2") then ["a"; "b"; "c"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "3") then ["d"; "e"; "f"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "4") then ["g"; "h"; "i"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "5") then ["j"; "k"; "l"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "6") then ["m"; "n"; "o"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "7") then ["p"; "q"; "r"; "s"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "8") then ["t"; "u"; "v"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "9") then ["w"; "x"; "y"; "z"]%char
  else [].

Definition list_ascii_eqb (l1 l2 : list ascii) : bool :=
  Nat.eqb (List.length l1) (List.length l2) && 
  forallb (fun p => Nat.eqb (nat_of_ascii (fst p)) (nat_of_ascii (snd p))) (combine l1 l2).

Fixpoint go (chars : list ascii) : list string :=
  match chars with
  | [] => []
  | d :: ds =>
    let restCombinations := go ds in
    let currentLetters := digitToLetters d in
    match restCombinations with
    | [] => map (fun c => String c EmptyString) currentLetters
    | _ => flat_map (fun c => map (fun s => String c s) restCombinations) currentLetters
    end
  end.

Definition anyInvalid (chars : list ascii) : bool :=
  existsb (fun c => list_ascii_eqb (digitToLetters c) []) chars.
(* !benchmark @end code_aux *)

Definition letterCombinations (digits : string) : (list string) :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string digits in
    if anyInvalid chars then []
    else go chars
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isValidDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  let n2 := nat_of_ascii "2" in
  let n9 := nat_of_ascii "9" in
  Nat.leb n2 n && Nat.leb n n9.

Definition digitToLetters_post (c : ascii) : list ascii :=
  if Nat.eqb (nat_of_ascii c) (nat_of_ascii "2") then ["a"; "b"; "c"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "3") then ["d"; "e"; "f"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "4") then ["g"; "h"; "i"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "5") then ["j"; "k"; "l"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "6") then ["m"; "n"; "o"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "7") then ["p"; "q"; "r"; "s"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "8") then ["t"; "u"; "v"]%char
  else if Nat.eqb (nat_of_ascii c) (nat_of_ascii "9") then ["w"; "x"; "y"; "z"]%char
  else [].

Definition computeExpected (chars : list ascii) : list string :=
  fold_left (fun acc ls => flat_map (fun s => map (fun c => append s (String c EmptyString)) ls) acc)
            (map digitToLetters_post chars) [EmptyString].

Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 rest1, String c2 rest2 => 
    Nat.eqb (nat_of_ascii c1) (nat_of_ascii c2) && string_eqb rest1 rest2
  | _, _ => false
  end.

Definition string_in_list (s : string) (l : list string) : bool :=
  existsb (fun x => string_eqb s x) l.
(* !benchmark @end postcond_aux *)

Definition letterCombinations_postcond (digits : string) (result : (list string)) : bool :=
  (* !benchmark @start postcond *)
  let chars := list_ascii_of_string digits in
      if Nat.eqb (List.length chars) 0 then
        Nat.eqb (List.length result) 0
      else if existsb (fun c => negb (isValidDigit c)) chars then
        Nat.eqb (List.length result) 0
      else
        let expected := computeExpected chars in
        Nat.eqb (List.length result) (List.length expected) &&
        forallb (fun s => string_in_list s expected) result &&
        forallb (fun s => string_in_list s result) expected
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem letterCombinations_postcond_satisfied (digits : string) :
    letterCombinations_precond digits = true ->
    letterCombinations_postcond digits (letterCombinations digits) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
