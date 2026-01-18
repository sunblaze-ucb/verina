(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SwapSimultaneous_precond_dec (X : Z) (Y : Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition SwapSimultaneous_precond (X : Z) (Y : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No code auxiliary definitions needed *)
(* !benchmark @end code_aux *)

Definition SwapSimultaneous (X : Z) (Y : Z) (h_precond : SwapSimultaneous_precond X Y) : (Z  * Z) :=
  (* !benchmark @start code *)
  (Y, X)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition SwapSimultaneous_postcond_dec (X : Z) (Y : Z) (result : Z * Z) : bool :=
  let '(r1, r2) := result in
  (r1 =? Y) && (r2 =? X) && 
  (if (X =? Y) then true else (negb (r1 =? X)) && (negb (r2 =? Y))).
(* !benchmark @end postcond_aux *)

Definition SwapSimultaneous_postcond (X : Z) (Y : Z) (result : (Z  * Z)) (h_precond : SwapSimultaneous_precond X Y) : Prop :=
  (* !benchmark @start postcond *)
  fst result = Y /\ snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SwapSimultaneous_postcond_satisfied (X : Z) (Y : Z) (h_precond : SwapSimultaneous_precond X Y) :
    SwapSimultaneous_postcond X Y (SwapSimultaneous X Y h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
