(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import Arith.
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

Definition containsZ_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition is_z (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 122 || Nat.eqb n 90.

Fixpoint any_is_z (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | c :: rest => if is_z c then true else any_is_z rest
  end.
(* !benchmark @end code_aux *)

Definition containsZ (s : string) : bool :=
  (* !benchmark @start code *)
  any_is_z (list_ascii_of_string s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition is_z_post (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 122 || Nat.eqb n 90.
(* !benchmark @end postcond_aux *)

Definition containsZ_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  Bool.eqb (existsb is_z_post cs) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem containsZ_postcond_satisfied (s : string) :
    containsZ_precond s = true ->
    containsZ_postcond s (containsZ s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
