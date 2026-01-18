(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import String.
Require Import List.
Require Import Ascii.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to split string on spaces *)
Fixpoint split_on_space (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c rest =>
    if (c =? " ")%char then
      EmptyString :: split_on_space rest
    else
      match split_on_space rest with
      | [] => [String c EmptyString]
      | hd :: tl => String c hd :: tl
      end
  end.

(* Helper to filter non-empty strings *)
Fixpoint filter_non_empty (words : list string) : list string :=
  match words with
  | [] => []
  | h :: t =>
    if (h =? "")%string then
      filter_non_empty t
    else
      h :: filter_non_empty t
  end.

(* Helper to join strings with spaces *)
Fixpoint join_with_space (words : list string) : string :=
  match words with
  | [] => EmptyString
  | [w] => w
  | h :: t => (h ++ " " ++ join_with_space t)%string
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition reverseWords_precond_dec (words_str : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition reverseWords_precond (words_str : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code auxiliaries needed *)
(* !benchmark @end code_aux *)

Definition reverseWords (words_str : string) (h_precond : reverseWords_precond words_str) : string :=
  (* !benchmark @start code *)
  let rawWords := split_on_space words_str in
let filteredWords := filter_non_empty rawWords in
let revWords := rev filteredWords in
let result := join_with_space revWords in
result
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* For decidable version, we'd need decidable equality on strings and lists *)
Definition reverseWords_postcond_dec (words_str : string) (result : string) : bool :=
  (* This is a placeholder - actual implementation would need proper string/list equality *)
  true.
(* !benchmark @end postcond_aux *)

Definition reverseWords_postcond (words_str : string) (result : string) (h_precond : reverseWords_precond words_str) : Prop :=
  (* !benchmark @start postcond *)
  exists words : list string,
  words = filter_non_empty (split_on_space words_str) /\
  result = join_with_space (rev words)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverseWords_postcond_satisfied (words_str : string) (h_precond : reverseWords_precond words_str) :
    reverseWords_postcond words_str (reverseWords words_str h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
