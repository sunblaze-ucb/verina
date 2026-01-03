(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition reverseWords_precond_dec (words_str : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition reverseWords_precond (words_str : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition reverseWords (words_str : string) (h_precond : reverseWords_precond words_str) : string :=
  (* !benchmark @start code *)
  ""
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition reverseWords_postcond_dec (words_str : string) (result : string) : bool := true.
(* !benchmark @end postcond_aux *)

Definition reverseWords_postcond (words_str : string) (result : string) (h_precond : reverseWords_precond words_str) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem reverseWords_postcond_satisfied (words_str : string) (h_precond : reverseWords_precond words_str) :
    reverseWords_postcond words_str (reverseWords words_str h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
