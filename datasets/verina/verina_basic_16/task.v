(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition replaceChars_precond_dec (s : string) (oldChar : ascii) (newChar : ascii) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition replaceChars_precond (s : string) (oldChar : ascii) (newChar : ascii) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint map_chars (cs : list ascii) (oldChar : ascii) (newChar : ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: tl => (if ascii_dec c oldChar then newChar else c) :: map_chars tl oldChar newChar
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Fixpoint list_to_string (cs : list ascii) : string :=
  match cs with
  | [] => EmptyString
  | c :: cs' => String c (list_to_string cs')
  end.
(* !benchmark @end code_aux *)

Definition replaceChars (s : string) (oldChar : ascii) (newChar : ascii) (h_precond : replaceChars_precond s oldChar newChar) : string :=
  (* !benchmark @start code *)
  let cs := string_to_list s in
  let cs' := map_chars cs oldChar newChar in
  list_to_string cs'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_ascii (cs : list ascii) (n : nat) : option ascii :=
  match cs with
  | [] => None
  | c :: tl => match n with
               | O => Some c
               | S n' => nth_ascii tl n'
               end
  end.

Definition replaceChars_postcond_dec (s : string) (oldChar : ascii) (newChar : ascii) (result : string) : bool :=
  let cs := string_to_list s in
  let cs' := string_to_list result in
  Nat.eqb (length cs') (length cs).
(* !benchmark @end postcond_aux *)

Definition replaceChars_postcond (s : string) (oldChar : ascii) (newChar : ascii) (result : string) (h_precond : replaceChars_precond s oldChar newChar) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
  let cs' := string_to_list result in
  (length cs' = length cs)%nat /\
  (forall i, (i < length cs)%nat ->
    (nth_ascii cs i = Some oldChar -> nth_ascii cs' i = Some newChar) /\
    (nth_ascii cs i <> Some oldChar -> nth_ascii cs' i = nth_ascii cs i))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replaceChars_postcond_satisfied (s : string) (oldChar : ascii) (newChar : ascii) (h_precond : replaceChars_precond s oldChar newChar) :
    replaceChars_postcond s oldChar newChar (replaceChars s oldChar newChar h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
