(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition containsConsecutiveNumbers_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition containsConsecutiveNumbers_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint containsConsecutiveNumbersHelper (l : list Z) : bool :=
  match l with
  | [] => false
  | [_] => false
  | x :: xs => 
      match xs with
      | [] => false
      | y :: _ => 
          if Z.eqb (x + 1) y then true
          else containsConsecutiveNumbersHelper xs
      end
  end.
(* !benchmark @end code_aux *)

Definition containsConsecutiveNumbers (a : (list Z)) (h_precond : containsConsecutiveNumbers_precond a) : bool :=
  (* !benchmark @start code *)
  containsConsecutiveNumbersHelper a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint existsConsecutivePair (l : list Z) : Prop :=
  match l with
  | [] => False
  | [_] => False
  | x :: (y :: _) as xs =>
      ((x + 1)%Z = y) \/
      existsConsecutivePair xs
  end.

Definition containsConsecutiveNumbers_postcond_dec (a : list Z) (result : bool) : bool :=
  Bool.eqb result (containsConsecutiveNumbersHelper a).
(* !benchmark @end postcond_aux *)

Definition containsConsecutiveNumbers_postcond (a : (list Z)) (result : bool) (h_precond : containsConsecutiveNumbers_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (exists i : nat, (i < length a - 1%nat)%nat /\ (nth i a 0%Z + 1)%Z = nth (i + 1%nat) a 0%Z) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem containsConsecutiveNumbers_postcond_satisfied (a : (list Z)) (h_precond : containsConsecutiveNumbers_precond a) :
    containsConsecutiveNumbers_postcond a (containsConsecutiveNumbers a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
