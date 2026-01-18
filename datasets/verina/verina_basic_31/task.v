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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition toUppercase_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition toUppercase_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isLowerCase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  let a_val := nat_of_ascii "a"%char in
  let z_val := nat_of_ascii "z"%char in
  andb (Nat.leb a_val n) (Nat.leb n z_val).

Definition shiftMinus32 (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  ascii_of_nat (Nat.modulo (n - 32) 128).

Fixpoint map_chars (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_chars f rest)
  end.
(* !benchmark @end code_aux *)

Definition toUppercase (s : string) (h_precond : toUppercase_precond s) : string :=
  (* !benchmark @start code *)
  map_chars (fun c => if isLowerCase c then shiftMinus32 c else c) s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0%nat
  | String _ rest => S (string_length rest)
  end.

Fixpoint nth_char (l : list ascii) (i : nat) : ascii :=
  match l, i with
  | [], _ => "!"%char
  | c :: _, 0%nat => c
  | _ :: rest, S i' => nth_char rest i'
  end.

Definition toUppercase_postcond_dec (s : string) (result : string) : bool :=
  let cs := string_to_list s in
  let cs' := string_to_list result in
  let len_eq := Nat.eqb (string_length result) (string_length s) in
  len_eq.
(* !benchmark @end postcond_aux *)

Definition toUppercase_postcond (s : string) (result : string) (h_precond : toUppercase_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
let cs' := string_to_list result in
(string_length result = string_length s) /\
(forall i, (i < string_length s)%nat ->
  (isLowerCase (nth_char cs i) = true -> nth_char cs' i = shiftMinus32 (nth_char cs i)) /\
  (isLowerCase (nth_char cs i) = false -> nth_char cs' i = nth_char cs i))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem toUppercase_postcond_satisfied (s : string) (h_precond : toUppercase_precond s) :
    toUppercase_postcond s (toUppercase s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
