(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to convert ascii to string *)
Definition ascii_to_string (c : ascii) : string :=
  String c EmptyString.

(* Helper for string append *)
Definition string_append (s1 s2 : string) : string :=
  (s1 ++ s2)%string.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition letterCombinations_precond_dec (digits : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition letterCombinations_precond (digits : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition digitToLetters (c : ascii) : list ascii :=
  if ascii_dec c "2"%char then ["a"%char; "b"%char; "c"%char]
  else if ascii_dec c "3"%char then ["d"%char; "e"%char; "f"%char]
  else if ascii_dec c "4"%char then ["g"%char; "h"%char; "i"%char]
  else if ascii_dec c "5"%char then ["j"%char; "k"%char; "l"%char]
  else if ascii_dec c "6"%char then ["m"%char; "n"%char; "o"%char]
  else if ascii_dec c "7"%char then ["p"%char; "q"%char; "r"%char; "s"%char]
  else if ascii_dec c "8"%char then ["t"%char; "u"%char; "v"%char]
  else if ascii_dec c "9"%char then ["w"%char; "x"%char; "y"%char; "z"%char]
  else [].

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Definition list_any {A : Type} (f : A -> bool) (l : list A) : bool :=
  existsb f l.

Definition list_null {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

Fixpoint go (chars : list ascii) : list string :=
  match chars with
  | [] => []
  | d :: ds =>
      let restCombinations := go ds in
      let currentLetters := digitToLetters d in
      match restCombinations with
      | [] => map ascii_to_string currentLetters
      | _ => flat_map (fun c => map (fun s => string_append (ascii_to_string c) s) restCombinations) currentLetters
      end
  end.
(* !benchmark @end code_aux *)

Definition letterCombinations (digits : string) (h_precond : letterCombinations_precond digits) : (list string) :=
  (* !benchmark @start code *)
  let chars := string_to_list digits in
  if list_any (fun c => list_null (digitToLetters c)) chars then []
  else go chars
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint foldl {A B : Type} (f : A -> B -> A) (acc : A) (l : list B) : A :=
  match l with
  | [] => acc
  | x :: xs => foldl f (f acc x) xs
  end.

Definition list_all {A : Type} (f : A -> bool) (l : list A) : bool :=
  forallb f l.

Definition string_mem (s : string) (l : list string) : bool :=
  existsb (fun x => if string_dec x s then true else false) l.

Definition string_empty (s : string) : bool :=
  match s with
  | EmptyString => true
  | _ => false
  end.

Definition char_mem (c : ascii) (l : list ascii) : bool :=
  existsb (fun x => if ascii_dec x c then true else false) l.

Definition letterCombinations_postcond_dec (digits : string) (result : list string) : bool :=
  if string_empty digits then
    list_null result
  else if list_any (fun c => negb (char_mem c ["2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char])) (string_to_list digits) then
    list_null result
  else
    let expected := foldl (fun acc ls => flat_map (fun s => map (fun c => string_append s (ascii_to_string c)) ls) acc)
                          [EmptyString]
                          (map digitToLetters (string_to_list digits)) in
    andb (andb (Nat.eqb (length result) (length expected))
               (list_all (fun s => string_mem s expected) result))
         (list_all (fun s => string_mem s result) expected).
(* !benchmark @end postcond_aux *)

Definition letterCombinations_postcond (digits : string) (result : (list string)) (h_precond : letterCombinations_precond digits) : Prop :=
  (* !benchmark @start postcond *)
  if string_empty digits then
    result = []
  else if list_any (fun c => negb (char_mem c ["2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char])) (string_to_list digits) then
    result = []
  else
    let expected := foldl (fun acc ls => flat_map (fun s => map (fun c => string_append s (ascii_to_string c)) ls) acc)
                          [EmptyString]
                          (map digitToLetters (string_to_list digits)) in
    length result = length expected /\ list_all (fun s => string_mem s expected) result = true /\ list_all (fun s => string_mem s result) expected = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem letterCombinations_postcond_satisfied (digits : string) (h_precond : letterCombinations_precond digits) :
    letterCombinations_postcond digits (letterCombinations digits h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
