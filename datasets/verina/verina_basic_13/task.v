(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition cubeElements_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition cubeElements_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers needed *)
(* !benchmark @end code_aux *)

Definition cubeElements (a : (list Z)) (h_precond : cubeElements_precond a) : (list Z) :=
  (* !benchmark @start code *)
  map (fun x => (x * x * x)%Z) a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint postcond_helper (result a : list Z) (i : nat) : Prop :=
  match i with
  | O => True
  | S i' =>
      postcond_helper result a i' /\
      match nth_error a i' with
      | Some a_i =>
          match nth_error result i' with
          | Some r_i => r_i = (a_i * a_i * a_i)%Z
          | None => False
          end
      | None => True
      end
  end.

Definition cubeElements_postcond_dec (a result : list Z) : bool :=
  Nat.eqb (length result) (length a).
(* !benchmark @end postcond_aux *)

Definition cubeElements_postcond (a : (list Z)) (result : (list Z)) (h_precond : cubeElements_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length a) /\
  (forall i : nat, (i < length a)%nat ->
    match nth_error result i, nth_error a i with
    | Some r_i, Some a_i => r_i = (a_i * a_i * a_i)%Z
    | _, _ => False
    end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem cubeElements_postcond_satisfied (a : (list Z)) (h_precond : cubeElements_precond a) :
    cubeElements_postcond a (cubeElements a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
