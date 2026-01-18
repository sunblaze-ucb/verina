(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution-level helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isSorted_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isSorted_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isSorted_helper (l : list Z) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: rest => 
      match rest with
      | [] => true
      | y :: _ => 
          if (x <=? y)%Z then isSorted_helper rest
          else false
      end
  end.
(* !benchmark @end code_aux *)

Definition isSorted (a : (list Z)) (h_precond : isSorted_precond a) : bool :=
  (* !benchmark @start code *)
  match a with
| [] => true
| [_] => true
| _ => isSorted_helper a
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n' default
  end.

Definition isSorted_postcond_dec (a : list Z) (result : bool) : bool :=
  result.
(* !benchmark @end postcond_aux *)

Definition isSorted_postcond (a : (list Z)) (result : bool) (h_precond : isSorted_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (forall i : nat, (i < Nat.pred (length a))%nat -> (nth_Z a i 0 <= nth_Z a (i + 1)%nat 0)%Z) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isSorted_postcond_satisfied (a : (list Z)) (h_precond : isSorted_precond a) :
    isSorted_postcond a (isSorted a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
