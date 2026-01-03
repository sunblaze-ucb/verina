(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition hasChordIntersection_precond_dec (N : nat) (chords : (list (list nat))) : bool := true.
(* !benchmark @end precond_aux *)

Definition hasChordIntersection_precond (N : nat) (chords : (list (list nat))) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition hasChordIntersection (N : nat) (chords : (list (list nat))) (h_precond : hasChordIntersection_precond N chords) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition hasChordIntersection_postcond_dec (N : nat) (chords : (list (list nat))) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition hasChordIntersection_postcond (N : nat) (chords : (list (list nat))) (result : bool) (h_precond : hasChordIntersection_precond N chords) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem hasChordIntersection_postcond_satisfied (N : nat) (chords : (list (list nat))) (h_precond : hasChordIntersection_precond N chords) :
    hasChordIntersection_postcond N chords (hasChordIntersection N chords h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
