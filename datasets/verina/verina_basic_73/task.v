(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
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
Definition Match_precond_dec (s : string) (p : string) : bool :=
  Nat.eqb (String.length s) (String.length p).
(* !benchmark @end precond_aux *)

Definition Match_precond (s : string) (p : string) : Prop :=
  (* !benchmark @start precond *)
  String.length s = String.length p
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (sList : list ascii) (pList : list ascii) (i : nat) : bool :=
  match i with
  | O => 
      match sList, pList with
      | [], [] => true
      | sh :: st, ph :: pt =>
          if andb (negb (Ascii.eqb sh ph)) (negb (Ascii.eqb ph "?"%char)) then false
          else loop st pt O
      | _, _ => true
      end
  | S i' => 
      match sList, pList with
      | sh :: st, ph :: pt => loop st pt i'
      | _, _ => true
      end
  end.
(* !benchmark @end code_aux *)

Definition Match (s : string) (p : string) (h_precond : Match_precond s p) : bool :=
  (* !benchmark @start code *)
  let sList := list_ascii_of_string s in
  let pList := list_ascii_of_string p in
  loop sList pList 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint all_match_dec (sList : list ascii) (pList : list ascii) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      andb (all_match_dec sList pList n')
           (match nth_error sList n', nth_error pList n' with
            | Some sc, Some pc => orb (Ascii.eqb sc pc) (Ascii.eqb pc "?"%char)
            | _, _ => true
            end)
  end.

Definition Match_postcond_dec (s : string) (p : string) (result : bool) : bool :=
  let sList := list_ascii_of_string s in
  let pList := list_ascii_of_string p in
  Bool.eqb result (all_match_dec sList pList (length sList)).
(* !benchmark @end postcond_aux *)

Definition Match_postcond (s : string) (p : string) (result : bool) (h_precond : Match_precond s p) : Prop :=
  (* !benchmark @start postcond *)
  let sList := list_ascii_of_string s in
  let pList := list_ascii_of_string p in
  (result = true <-> forall n : nat, (n < length sList)%nat -> 
    match nth_error sList n, nth_error pList n with
    | Some sc, Some pc => sc = pc \/ pc = "?"%char
    | _, _ => True
    end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Match_postcond_satisfied (s : string) (p : string) (h_precond : Match_precond s p) :
    Match_postcond s p (Match s p h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
