(* !benchmark @start import type=task *)
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
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Definition isOdd (n : Z) : bool :=
  negb (isEven n).

Fixpoint findIdx_aux {A : Type} (p : A -> bool) (lst : list A) (idx : nat) : option nat :=
  match lst with
  | [] => None
  | x :: xs => if p x then Some idx else findIdx_aux p xs (S idx)
  end.

Definition findIdx {A : Type} (p : A -> bool) (lst : list A) : option nat :=
  findIdx_aux p lst 0%nat.

Definition firstEvenOddIndices (lst : list Z) : option (nat * nat) :=
  let evenIndex := findIdx isEven lst in
  let oddIndex := findIdx isOdd lst in
  match evenIndex, oddIndex with
  | Some ei, Some oi => Some (ei, oi)
  | _, _ => None
  end.

Fixpoint existsb_prop (p : Z -> bool) (lst : list Z) : Prop :=
  match lst with
  | [] => False
  | x :: xs => p x = true \/ existsb_prop p xs
  end.

Definition findProduct_precond_dec (lst : list Z) : bool :=
  ((length lst >? 1)%nat) && existsb isEven lst && existsb isOdd lst.
(* !benchmark @end precond_aux *)

Definition findProduct_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  ((length lst) > 1)%nat /\
  (exists x, In x lst /\ isEven x = true) /\
  (exists x, In x lst /\ isOdd x = true)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to get nth element with default *)
Fixpoint nth_default {A : Type} (default : A) (lst : list A) (n : nat) : A :=
  match n, lst with
  | O, x :: _ => x
  | S m, _ :: xs => nth_default default xs m
  | _, [] => default
  end.
(* !benchmark @end code_aux *)

Definition findProduct (lst : (list Z)) (h_precond : findProduct_precond lst) : Z :=
  (* !benchmark @start code *)
  match firstEvenOddIndices lst with
  | Some (ei, oi) => (nth_default 0 lst ei * nth_default 0 lst oi)%Z
  | None => 0%Z
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findProduct_postcond_dec (lst : list Z) (result : Z) : bool :=
  match firstEvenOddIndices lst with
  | Some (ei, oi) => (result =? (nth_default 0 lst ei * nth_default 0 lst oi))%Z
  | None => true
  end.
(* !benchmark @end postcond_aux *)

Definition findProduct_postcond (lst : (list Z)) (result : Z) (h_precond : findProduct_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  match firstEvenOddIndices lst with
  | Some (ei, oi) => result = (nth_default 0 lst ei * nth_default 0 lst oi)%Z
  | None => True
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findProduct_postcond_satisfied (lst : (list Z)) (h_precond : findProduct_precond lst) :
    findProduct_postcond lst (findProduct lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
