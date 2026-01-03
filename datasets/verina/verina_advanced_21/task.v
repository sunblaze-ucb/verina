(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition isPalindrome_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition isPalindrome_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition isPalindrome (s : string) (h_precond : isPalindrome_precond s) : bool :=
  (* !benchmark @start code *)
  true
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isPalindrome_postcond_dec (s : string) (result : bool) : bool := true.
(* !benchmark @end postcond_aux *)

Definition isPalindrome_postcond (s : string) (result : bool) (h_precond : isPalindrome_precond s) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem isPalindrome_postcond_satisfied (s : string) (h_precond : isPalindrome_precond s) :
    isPalindrome_postcond s (isPalindrome s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
