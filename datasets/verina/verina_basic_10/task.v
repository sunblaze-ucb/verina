(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import ZArith.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level helper definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isGreater_precond_dec (n : Z) (a : list Z) : bool :=
  match length a with
  | O => false
  | S _ => true
  end.
(* !benchmark @end precond_aux *)

Definition isGreater_precond (n : Z) (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint all_greater (n : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => if (n >? x) then all_greater n xs else false
  end.
(* !benchmark @end code_aux *)

Definition isGreater (n : Z) (a : (list Z)) (h_precond : isGreater_precond n a) : bool :=
  (* !benchmark @start code *)
  all_greater n a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isGreater_postcond_dec (n : Z) (a : list Z) (result : bool) : bool :=
  let check_all := all_greater n a in
  Bool.eqb result check_all.
(* !benchmark @end postcond_aux *)

Definition isGreater_postcond (n : Z) (a : (list Z)) (result : bool) (h_precond : isGreater_precond n a) : Prop :=
  (* !benchmark @start postcond *)
  (forall i : nat, (i < length a)%nat -> n > nth i a 0) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isGreater_postcond_satisfied (n : Z) (a : (list Z)) (h_precond : isGreater_precond n a) :
    isGreater_postcond n a (isGreater n a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
