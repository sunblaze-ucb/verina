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
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Definition isOdd (n : Z) : bool :=
  negb (n mod 2 =? 0)%Z.

Fixpoint exists_in_list (f : Z -> bool) (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: xs => if f x then true else exists_in_list f xs
  end.

Definition firstEvenOddDifference_precond_dec (a : list Z) : bool :=
  ((Nat.ltb 1 (length a)) && exists_in_list isEven a && exists_in_list isOdd a)%bool.
(* !benchmark @end precond_aux *)

Definition firstEvenOddDifference_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 1)%nat /\
  (exists x, In x a /\ isEven x = true) /\
  (exists x, In x a /\ isOdd x = true)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S m => nth_Z xs m default
  end.

Fixpoint findFirstEvenOdd_fuel (a : list Z) (fuel i : nat) (firstEven firstOdd : option nat) : Z :=
  match fuel with
  | O => 0%Z
  | S fuel' =>
      match Nat.compare i (length a) with
      | Lt =>
          let x := nth_Z a i 0%Z in
          let firstEven := match firstEven with
                           | None => if isEven x then Some i else None
                           | Some e => Some e
                           end in
          let firstOdd := match firstOdd with
                          | None => if isOdd x then Some i else None
                          | Some o => Some o
                          end in
          match firstEven, firstOdd with
          | Some e, Some o => (nth_Z a e 0%Z - nth_Z a o 0%Z)%Z
          | _, _ => findFirstEvenOdd_fuel a fuel' (S i) firstEven firstOdd
          end
      | _ => 0%Z
      end
  end.

Definition findFirstEvenOdd (a : list Z) (i : nat) (firstEven firstOdd : option nat) : Z :=
  findFirstEvenOdd_fuel a (length a) i firstEven firstOdd.
(* !benchmark @end code_aux *)

Definition firstEvenOddDifference (a : (list Z)) (h_precond : firstEvenOddDifference_precond a) : Z :=
  (* !benchmark @start code *)
  findFirstEvenOdd a 0%nat None None
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition firstEvenOddDifference_postcond_dec (a : list Z) (result : Z) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition firstEvenOddDifference_postcond (a : (list Z)) (result : Z) (h_precond : firstEvenOddDifference_precond a) : Prop :=
  (* !benchmark @start postcond *)
  exists i j,
  (i < length a)%nat /\ (j < length a)%nat /\
  isEven (nth_Z a i 0%Z) = true /\
  isOdd (nth_Z a j 0%Z) = true /\
  result = (nth_Z a i 0%Z - nth_Z a j 0%Z)%Z /\
  (forall k, (k < i)%nat -> isOdd (nth_Z a k 0%Z) = true) /\
  (forall k, (k < j)%nat -> isEven (nth_Z a k 0%Z) = true)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem firstEvenOddDifference_postcond_satisfied (a : (list Z)) (h_precond : firstEvenOddDifference_precond a) :
    firstEvenOddDifference_postcond a (firstEvenOddDifference a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
