(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition insert_precond_dec (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition insert_precond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition insert (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (h_precond : insert_precond oline l nl p atPos) : (list ascii) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition insert_postcond_dec (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (result : (list ascii)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition insert_postcond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (result : (list ascii)) (h_precond : insert_precond oline l nl p atPos) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem insert_postcond_satisfied (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (h_precond : insert_precond oline l nl p atPos) :
    insert_postcond oline l nl p atPos (insert oline l nl p atPos h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
