(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition findFirstRepeatedChar_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition findFirstRepeatedChar_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findFirstRepeatedChar (s : string) (h_precond : findFirstRepeatedChar_precond s) : (option ascii) :=
  (* !benchmark @start code *)
  None
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findFirstRepeatedChar_postcond_dec (s : string) (result : (option ascii)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition findFirstRepeatedChar_postcond (s : string) (result : (option ascii)) (h_precond : findFirstRepeatedChar_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem findFirstRepeatedChar_postcond_satisfied (s : string) (h_precond : findFirstRepeatedChar_precond s) :
    findFirstRepeatedChar_postcond s (findFirstRepeatedChar s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
