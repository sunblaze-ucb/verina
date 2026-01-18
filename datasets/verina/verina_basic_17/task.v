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
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Nat.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition toLowercase_precond_dec (s : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition toLowercase_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isUpperCase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "A"%char in
  let z := nat_of_ascii "Z"%char in
  Nat.leb a n && Nat.leb n z.

Definition shift32 (c : ascii) : ascii :=
  ascii_of_nat (nat_of_ascii c + 32).

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_string f rest)
  end.
(* !benchmark @end code_aux *)

Definition toLowercase (s : string) (h_precond : toLowercase_precond s) : string :=
  (* !benchmark @start code *)
  map_string (fun c => if isUpperCase c then shift32 c else c) s
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

Fixpoint list_nth_default {A : Type} (l : list A) (n : nat) (default : A) : A :=
  match n, l with
  | 0%nat, x :: _ => x
  | S m, _ :: t => list_nth_default t m default
  | _, [] => default
  end.

Definition toLowercase_postcond_dec (s : string) (result : string) : bool :=
  let cs := string_to_list s in
  let cs' := string_to_list result in
  let len_eq := Nat.eqb (string_length result) (string_length s) in
  len_eq.
(* !benchmark @end postcond_aux *)

Definition toLowercase_postcond (s : string) (result : string) (h_precond : toLowercase_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
let cs' := string_to_list result in
(string_length result = string_length s) /\
(forall i : nat, (i < string_length s)%nat ->
  (isUpperCase (list_nth_default cs i "000"%char) = true -> 
   list_nth_default cs' i "000"%char = shift32 (list_nth_default cs i "000"%char)) /\
  (isUpperCase (list_nth_default cs i "000"%char) = false -> 
   list_nth_default cs' i "000"%char = list_nth_default cs i "000"%char))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem toLowercase_postcond_satisfied (s : string) (h_precond : toLowercase_precond s) :
    toLowercase_postcond s (toLowercase s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
