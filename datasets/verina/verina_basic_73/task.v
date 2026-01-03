(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition Match_precond_dec (s : string) (p : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition Match_precond (s : string) (p : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition Match (s : string) (p : string) (h_precond : Match_precond s p) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Match_postcond_dec (s : string) (p : string) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition Match_postcond (s : string) (p : string) (result : bool) (h_precond : Match_precond s p) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem Match_postcond_satisfied (s : string) (p : string) (h_precond : Match_precond s p) :
    Match_postcond s p (Match s p h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
