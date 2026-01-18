(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to check list equality *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => Ascii.eqb h1 h2 && list_ascii_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition reverseString_precond_dec (s : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition reverseString_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint reverseAux (chars : list ascii) (acc : list ascii) : list ascii :=
  match chars with
  | [] => acc
  | h :: t => reverseAux t (h :: acc)
  end.
(* !benchmark @end code_aux *)

Definition reverseString (s : string) (h_precond : reverseString_precond s) : string :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string s in
  string_of_list_ascii (reverseAux chars [])
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition reverseString_postcond_dec (s : string) (result : string) : bool :=
  Nat.eqb (String.length result) (String.length s) &&
  list_ascii_eqb (list_ascii_of_string result) (rev (list_ascii_of_string s)).
(* !benchmark @end postcond_aux *)

Definition reverseString_postcond (s : string) (result : string) (h_precond : reverseString_precond s) : Prop :=
  (* !benchmark @start postcond *)
  String.length result = String.length s /\ 
list_ascii_of_string result = rev (list_ascii_of_string s)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverseString_postcond_satisfied (s : string) (h_precond : reverseString_precond s) :
    reverseString_postcond s (reverseString s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
