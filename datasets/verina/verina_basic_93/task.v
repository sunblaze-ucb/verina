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

Definition SwapBitvectors_precond (X : Z) (Y : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition SwapBitvectors (X : Z) (Y : Z) : (Z * Z) :=
  (* !benchmark @start code *)
  let temp := Z.lxor X Y in
  let newY := Z.lxor temp Y in
  let newX := Z.lxor temp newY in
  (newX, newY)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)

(* !benchmark @end postcond_aux *)

Definition SwapBitvectors_postcond (X : Z) (Y : Z) (result : (Z * Z)) : bool :=
  (* !benchmark @start postcond *)
  ((fst result =? Y) && (snd result =? X) && implb (negb (X =? Y)) ((negb (fst result =? X)) && (negb (snd result =? Y))))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapBitvectors_postcond_satisfied (X : Z) (Y : Z) :
    SwapBitvectors_precond X Y = true ->
    SwapBitvectors_postcond X Y (SwapBitvectors X Y) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
