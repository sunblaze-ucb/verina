(* !benchmark @start import type=task *)
Require Import String.
Require Import List.
Require Import Ascii.
Require Import Bool.
Import ListNotations.
Open Scope string_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 t1, String c2 t2 => (Ascii.eqb c1 c2) && string_eqb t1 t2
  | _, _ => false
  end.

Fixpoint splitOnSpace_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => [acc]
  | String c rest =>
    if Ascii.eqb c " "%char then
      acc :: splitOnSpace_aux rest EmptyString
    else
      splitOnSpace_aux rest (acc ++ String c EmptyString)
  end.

Definition splitOnSpace (s : string) : list string :=
  splitOnSpace_aux s EmptyString.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition reverseWords_precond (words_str : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint filterNonEmpty (words : list string) : list string :=
  match words with
  | [] => []
  | h :: t =>
    if string_eqb h EmptyString then
      filterNonEmpty t
    else
      h :: filterNonEmpty t
  end.

Fixpoint joinWithSpace (words : list string) : string :=
  match words with
  | [] => EmptyString
  | [w] => w
  | h :: t => h ++ " " ++ joinWithSpace t
  end.
(* !benchmark @end code_aux *)

Definition reverseWords (words_str : string) : string :=
  (* !benchmark @start code *)
  let rawWords := splitOnSpace words_str in
  let filteredWords := filterNonEmpty rawWords in
  let revWords := rev filteredWords in
  joinWithSpace revWords
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_string_eqb (l1 l2 : list string) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => string_eqb h1 h2 && list_string_eqb t1 t2
  | _, _ => false
  end.

Definition filterWords (words : list string) : list string :=
  filter (fun w => negb (string_eqb w EmptyString)) words.

Fixpoint intercalate_space (words : list string) : string :=
  match words with
  | [] => EmptyString
  | [w] => w
  | h :: t => h ++ " " ++ intercalate_space t
  end.
(* !benchmark @end postcond_aux *)

Definition reverseWords_postcond (words_str : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let words := filterWords (splitOnSpace words_str) in
  string_eqb result (intercalate_space (rev words))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverseWords_postcond_satisfied (words_str : string) :
    reverseWords_precond words_str = true ->
    reverseWords_postcond words_str (reverseWords words_str) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
