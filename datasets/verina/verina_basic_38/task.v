(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
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

Definition allCharactersSame_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint all_same_char (c : ascii) (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | x :: xs => (Ascii.eqb x c) && all_same_char c xs
  end.

Definition allCharactersSameHelper (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | c :: rest => all_same_char c rest
  end.
(* !benchmark @end code_aux *)

Definition allCharactersSame (s : string) : bool :=
  (* !benchmark @start code *)
  allCharactersSameHelper (list_ascii_of_string s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_pairwise_eq (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => Ascii.eqb x y && list_pairwise_eq xs
    end
  end.

Fixpoint any_different_from_first (first : ascii) (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | x :: xs => negb (Ascii.eqb x first) || any_different_from_first first xs
  end.

Definition get_first_char (cs : list ascii) : ascii :=
  match cs with
  | [] => "000"%char
  | c :: _ => c
  end.

Definition list_ascii_nonempty (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | _ :: _ => true
  end.
(* !benchmark @end postcond_aux *)

Definition allCharactersSame_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  implb result (list_pairwise_eq cs) &&
  implb (negb result) (list_ascii_nonempty cs && any_different_from_first (get_first_char cs) cs)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allCharactersSame_postcond_satisfied (s : string) :
    allCharactersSame_precond s = true ->
    allCharactersSame_postcond s (allCharactersSame s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
