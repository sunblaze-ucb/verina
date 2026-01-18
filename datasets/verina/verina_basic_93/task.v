(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliaries *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SwapBitvectors_precond_dec (X : Z) (Y : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition SwapBitvectors_precond (X : Z) (Y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliaries *)
(* !benchmark @end code_aux *)

Definition SwapBitvectors (X : Z) (Y : Z) (h_precond : SwapBitvectors_precond X Y) : (Z * Z) :=
  (* !benchmark @start code *)
  let temp := Z.lxor X Y in
  let newY := Z.lxor temp Y in
  let newX := Z.lxor temp newY in
  (newX, newY)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SwapBitvectors_postcond_dec (X : Z) (Y : Z) (result : Z * Z) : bool :=
  let '(fst_result, snd_result) := result in
  (fst_result =? Y) && (snd_result =? X) &&
  (if (X =? Y) then true else (negb (fst_result =? X)) && (negb (snd_result =? Y))).
(* !benchmark @end postcond_aux *)

Definition SwapBitvectors_postcond (X : Z) (Y : Z) (result : (Z * Z)) (h_precond : SwapBitvectors_precond X Y) : Prop :=
  (* !benchmark @start postcond *)
  fst result = Y /\ snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapBitvectors_postcond_satisfied (X : Z) (Y : Z) (h_precond : SwapBitvectors_precond X Y) :
    SwapBitvectors_postcond X Y (SwapBitvectors X Y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
