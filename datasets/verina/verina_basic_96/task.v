(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition SwapSimultaneous_precond (X : Z) (Y : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition SwapSimultaneous (X : Z) (Y : Z) : (Z  * Z) :=
  (* !benchmark @start code *)
  (Y, X)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition SwapSimultaneous_postcond (X : Z) (Y : Z) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  (fst result =? Y) && (snd result =? X) && implb (negb (X =? Y)) ((negb (fst result =? X)) && (negb (snd result =? Y)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapSimultaneous_postcond_satisfied (X : Z) (Y : Z) :
    SwapSimultaneous_precond X Y = true ->
    SwapSimultaneous_postcond X Y (SwapSimultaneous X Y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
