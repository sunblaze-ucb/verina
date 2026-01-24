(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition cubeElements_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition cubeElements (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  map (fun x => x * x * x) a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z (n : nat) (l : list Z) (d : Z) : Z :=
  match l with
  | [] => d
  | h :: t => match n with
              | O => h
              | S n' => nth_default_Z n' t d
              end
  end.

Fixpoint forallb_indexed_aux (f : nat -> bool) (start : nat) (len : nat) : bool :=
  match len with
  | O => true
  | S len' => f start && forallb_indexed_aux f (S start) len'
  end.

Definition forallb_indexed (f : nat -> bool) (len : nat) : bool :=
  forallb_indexed_aux f O len.
(* !benchmark @end postcond_aux *)

Definition cubeElements_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a)%nat) &&
  forallb_indexed (fun i =>
    let ai := nth_default_Z i a 0 in
    let ri := nth_default_Z i result 0 in
    (ri =? ai * ai * ai)%Z
  ) (length a)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem cubeElements_postcond_satisfied (a : (list Z)) :
    cubeElements_precond a = true ->
    cubeElements_postcond a (cubeElements a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
