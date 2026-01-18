(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition Swap_precond_dec (X : Z) (Y : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition Swap_precond (X : Z) (Y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions *)
(* !benchmark @end code_aux *)

Definition Swap (X : Z) (Y : Z) (h_precond : Swap_precond X Y) : (Z  * Z) :=
  (* !benchmark @start code *)
  let x := X in
  let y := Y in
  let tmp := x in
  let x := y in
  let y := tmp in
  (x, y)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition Swap_postcond_dec (X : Z) (Y : Z) (result : Z * Z) : bool :=
  let fst_val := fst result in
  let snd_val := snd result in
  (fst_val =? Y)%Z && (snd_val =? X)%Z &&
  (if (X =? Y)%Z then true else (negb (fst_val =? X)%Z) && (negb (snd_val =? Y)%Z)).
(* !benchmark @end postcond_aux *)

Definition Swap_postcond (X : Z) (Y : Z) (result : (Z  * Z)) (h_precond : Swap_precond X Y) : Prop :=
  (* !benchmark @start postcond *)
  fst result = Y /\ snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Swap_postcond_satisfied (X : Z) (Y : Z) (h_precond : Swap_precond X Y) :
    Swap_postcond X Y (Swap X Y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
