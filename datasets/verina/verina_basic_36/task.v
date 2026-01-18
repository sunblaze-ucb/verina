(* !benchmark @start import type=task *)
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
(* Helper function to check if a character is space, comma, or dot *)
Definition isSpaceCommaDot (c : ascii) : bool :=
  if ascii_dec c " "%char then true
  else if ascii_dec c ","%char then true
  else if ascii_dec c "."%char then true
  else false.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition replaceWithColon_precond_dec (s : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition replaceWithColon_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to map a function over a string by converting to list and back *)
Fixpoint map_string_chars (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_string_chars f rest)
  end.
(* !benchmark @end code_aux *)

Definition replaceWithColon (s : string) (h_precond : replaceWithColon_precond s) : string :=
  (* !benchmark @start code *)
  map_string_chars (fun c => if isSpaceCommaDot c then ":"%char else c) s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to convert string to list of ascii chars *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

(* Helper to get length of string *)
Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0%nat
  | String _ rest => S (string_length rest)
  end.

(* Helper to get nth character of string *)
Fixpoint string_get (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String c _, 0%nat => Some c
  | String _ rest, S n' => string_get rest n'
  end.

Definition replaceWithColon_postcond_dec (s result : string) : bool :=
  Nat.eqb (string_length result) (string_length s).
(* !benchmark @end postcond_aux *)

Definition replaceWithColon_postcond (s : string) (result : string) (h_precond : replaceWithColon_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
let cs' := string_to_list result in
string_length result = string_length s /\
(forall i, (i < string_length s)%nat ->
  (forall c, string_get s i = Some c ->
    (isSpaceCommaDot c = true -> string_get result i = Some ":"%char) /\
    (isSpaceCommaDot c = false -> string_get result i = Some c)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replaceWithColon_postcond_satisfied (s : string) (h_precond : replaceWithColon_precond s) :
    replaceWithColon_postcond s (replaceWithColon s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
