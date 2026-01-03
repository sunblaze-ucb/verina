(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition longestCommonSubsequence_precond_dec (s1 : string) (s2 : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestCommonSubsequence_precond (s1 : string) (s2 : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition longestCommonSubsequence (s1 : string) (s2 : string) (h_precond : longestCommonSubsequence_precond s1 s2) : string :=
  (* !benchmark @start code *)
  ""
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestCommonSubsequence_postcond_dec (s1 : string) (s2 : string) (result : string) : bool := true.
(* !benchmark @end postcond_aux *)

Definition longestCommonSubsequence_postcond (s1 : string) (s2 : string) (result : string) (h_precond : longestCommonSubsequence_precond s1 s2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem longestCommonSubsequence_postcond_satisfied (s1 : string) (s2 : string) (h_precond : longestCommonSubsequence_precond s1 s2) :
    longestCommonSubsequence_postcond s1 s2 (longestCommonSubsequence s1 s2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
