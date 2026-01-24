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

Definition SwapArithmetic_precond (X : Z) (Y : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition SwapArithmetic (X : Z) (Y : Z) : (Z  * Z) :=
  (* !benchmark @start code *)
  let x1 := X in
  let y1 := Y in
  let x2 := y1 - x1 in
  let y2 := y1 - x2 in
  let x3 := y2 + x2 in
  (x3, y2)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition SwapArithmetic_postcond (X : Z) (Y : Z) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  ((fst result =? Y) && (snd result =? X) && implb (negb (X =? Y)) ((negb (fst result =? X)) && (negb (snd result =? Y))))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapArithmetic_postcond_satisfied (X : Z) (Y : Z) :
    SwapArithmetic_precond X Y = true ->
    SwapArithmetic_postcond X Y (SwapArithmetic X Y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
