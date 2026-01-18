(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition findFirstOdd_precond_dec (a : list Z) : bool :=
  Nat.ltb 0%nat (length a).
(* !benchmark @end precond_aux *)

Definition findFirstOdd_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isOdd (x : Z) : bool :=
  negb (Z.eqb (x mod 2)%Z 0%Z).

Fixpoint find_index_aux {A : Type} (f : A -> bool) (l : list A) (idx : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if f x then Some idx else find_index_aux f xs (S idx)
  end.

Definition find_index {A : Type} (f : A -> bool) (l : list A) : option nat :=
  find_index_aux f l 0%nat.
(* !benchmark @end code_aux *)

Definition findFirstOdd (a : (list Z)) (h_precond : findFirstOdd_precond a) : (option nat) :=
  (* !benchmark @start code *)
  find_index isOdd a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, 0%nat => x
  | _ :: xs, S m => nth_Z xs m
  end.

Definition findFirstOdd_postcond_dec (a : list Z) (result : option nat) : bool :=
  match result with
  | Some idx =>
      (Nat.ltb idx (length a)) &&
      (isOdd (nth_Z a idx)) &&
      (forallb (fun j => negb (isOdd (nth_Z a j))) (seq 0 idx))
  | None =>
      forallb (fun i => negb (isOdd (nth_Z a i))) (seq 0 (length a))
  end.
(* !benchmark @end postcond_aux *)

Definition findFirstOdd_postcond (a : (list Z)) (result : (option nat)) (h_precond : findFirstOdd_precond a) : Prop :=
  (* !benchmark @start postcond *)
  match result with
| Some idx => 
    (idx < length a)%nat /\ 
    isOdd (nth_Z a idx) = true /\
    (forall j, (j < idx)%nat -> isOdd (nth_Z a j) = false)
| None => 
    forall i, (i < length a)%nat -> isOdd (nth_Z a i) = false
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstOdd_postcond_satisfied (a : (list Z)) (h_precond : findFirstOdd_precond a) :
    findFirstOdd_postcond a (findFirstOdd a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
