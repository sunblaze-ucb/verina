(* !benchmark @start import type=task *)
Require Import Bool.
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
Definition allCharactersSame_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition allCharactersSame_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint all_chars_equal (c : ascii) (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | x :: xs => if ascii_dec x c then all_chars_equal c xs else false
  end.

Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.
(* !benchmark @end code_aux *)

Definition allCharactersSame (s : string) (h_precond : allCharactersSame_precond s) : bool :=
  (* !benchmark @start code *)
  match string_to_list s with
| [] => true
| c :: cs => all_chars_equal c cs
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_pairwise_equal (cs : list ascii) : Prop :=
  match cs with
  | [] => True
  | c :: cs' => (forall x, In x cs' -> x = c) /\ list_pairwise_equal cs'
  end.

Fixpoint list_any_ne (c : ascii) (cs : list ascii) : Prop :=
  match cs with
  | [] => False
  | x :: xs => x <> c \/ list_any_ne c xs
  end.

Definition allCharactersSame_postcond_dec (s : string) (result : bool) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition allCharactersSame_postcond (s : string) (result : bool) (h_precond : allCharactersSame_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
  (result = true -> list_pairwise_equal cs) /\
  (result = false -> (cs <> [] /\ match cs with
                                   | [] => False
                                   | c :: _ => list_any_ne c cs
                                   end))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allCharactersSame_postcond_satisfied (s : string) (h_precond : allCharactersSame_precond s) :
    allCharactersSame_postcond s (allCharactersSame s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
