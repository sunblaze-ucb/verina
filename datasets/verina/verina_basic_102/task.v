(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition twoSum_precond_dec (nums : (list Z)) (target : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) : (nat  * nat) :=
  (* !benchmark @start code *)
  (0%nat, 0%nat)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition twoSum_postcond_dec (nums : (list Z)) (target : Z) (result : (nat  * nat)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (nat  * nat)) (h_precond : twoSum_precond nums target) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.