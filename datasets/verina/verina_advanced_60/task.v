(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition partitionEvensOdds_precond_dec (nums : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition partitionEvensOdds_precond (nums : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition partitionEvensOdds (nums : (list nat)) (h_precond : partitionEvensOdds_precond nums) : (list (nat  * (list nat))) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition partitionEvensOdds_postcond_dec (nums : (list nat)) (result : (list (nat  * (list nat)))) : bool := true.
(* !benchmark @end postcond_aux *)

Definition partitionEvensOdds_postcond (nums : (list nat)) (result : (list (nat  * (list nat)))) (h_precond : partitionEvensOdds_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem partitionEvensOdds_postcond_satisfied (nums : (list nat)) (h_precond : partitionEvensOdds_precond nums) :
    partitionEvensOdds_postcond nums (partitionEvensOdds nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
