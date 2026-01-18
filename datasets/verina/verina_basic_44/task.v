(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition isOdd (n : Z) : bool :=
  (n mod 2 =? 1)%Z.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isOddAtIndexOdd_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isOddAtIndexOdd_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint indexedList_aux {A : Type} (l : list A) (idx : nat) : list (nat * A) :=
  match l with
  | [] => []
  | x :: xs => (idx, x) :: indexedList_aux xs (S idx)
  end.

Definition indexedList {A : Type} (l : list A) : list (nat * A) :=
  indexedList_aux l 0%nat.

Fixpoint all_pairs (l : list (nat * Z)) : bool :=
  match l with
  | [] => true
  | (i, x) :: xs => 
      (negb (Nat.odd i) || isOdd x) && all_pairs xs
  end.
(* !benchmark @end code_aux *)

Definition isOddAtIndexOdd (a : (list Z)) (h_precond : isOddAtIndexOdd_precond a) : bool :=
  (* !benchmark @start code *)
  let indexedArray := indexedList a in
  all_pairs indexedArray
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint isOddAtIndexOdd_postcond_dec (a : list Z) (result : bool) : bool :=
  let fix check_indices (idx : nat) (l : list Z) : bool :=
    match l with
    | [] => true
    | x :: xs =>
        if Nat.odd idx
        then (isOdd x && check_indices (S idx) xs)%bool
        else check_indices (S idx) xs
    end
  in Bool.eqb result (check_indices 0%nat a).
(* !benchmark @end postcond_aux *)

Definition isOddAtIndexOdd_postcond (a : (list Z)) (result : bool) (h_precond : isOddAtIndexOdd_precond a) : Prop :=
  (* !benchmark @start postcond *)
  result = true <-> (forall i : nat, (i < length a)%nat -> Nat.odd i = true -> isOdd (nth i a 0%Z) = true)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isOddAtIndexOdd_postcond_satisfied (a : (list Z)) (h_precond : isOddAtIndexOdd_precond a) :
    isOddAtIndexOdd_postcond a (isOddAtIndexOdd a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
