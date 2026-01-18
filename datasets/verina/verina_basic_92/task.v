(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* empty *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SwapArithmetic_precond_dec (X : Z) (Y : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition SwapArithmetic_precond (X : Z) (Y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* empty *)
(* !benchmark @end code_aux *)

Definition SwapArithmetic (X : Z) (Y : Z) (h_precond : SwapArithmetic_precond X Y) : (Z  * Z) :=
  (* !benchmark @start code *)
  let x1 := X in
let y1 := Y in
let x2 := y1 - x1 in
let y2 := y1 - x2 in
let x3 := y2 + x2 in
(x3, y2)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SwapArithmetic_postcond_dec (X : Z) (Y : Z) (result : Z * Z) : bool :=
  let '(r1, r2) := result in
  (r1 =? Y)%Z && (r2 =? X)%Z &&
  (if (X =? Y)%Z then true else (negb (r1 =? X)%Z && negb (r2 =? Y)%Z)).
(* !benchmark @end postcond_aux *)

Definition SwapArithmetic_postcond (X : Z) (Y : Z) (result : (Z  * Z)) (h_precond : SwapArithmetic_precond X Y) : Prop :=
  (* !benchmark @start postcond *)
  fst result = Y /\ snd result = X /\
(X <> Y -> fst result <> X /\ snd result <> Y)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapArithmetic_postcond_satisfied (X : Z) (Y : Z) (h_precond : SwapArithmetic_precond X Y) :
    SwapArithmetic_postcond X Y (SwapArithmetic X Y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
