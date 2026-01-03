(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition binaryToDecimal_precond_dec (digits : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition binaryToDecimal_precond (digits : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition binaryToDecimal (digits : (list nat)) (h_precond : binaryToDecimal_precond digits) : nat :=
  (* !benchmark @start code *)
  0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition binaryToDecimal_postcond_dec (digits : (list nat)) (result : nat) : bool := true.
(* !benchmark @end postcond_aux *)

Definition binaryToDecimal_postcond (digits : (list nat)) (result : nat) (h_precond : binaryToDecimal_precond digits) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem binaryToDecimal_postcond_satisfied (digits : (list nat)) (h_precond : binaryToDecimal_precond digits) :
    binaryToDecimal_postcond digits (binaryToDecimal digits h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
