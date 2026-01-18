(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to compute sum of natural numbers *)
Fixpoint sum_nat (l : list nat) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => (x + sum_nat xs)%nat
  end.

(* Helper function to generate range [0..n] *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => [0%nat]
  | S m => range m ++ [n]
  end.

(* Helper to check if all elements satisfy a predicate *)
Fixpoint all {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => (p x && all p xs)%bool
  end.

(* Helper to check list membership *)
Fixpoint mem_nat (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => (Nat.eqb x y || mem_nat x ys)%bool
  end.

(* NoDup check *)
Fixpoint nodup_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => (negb (mem_nat x xs) && nodup_nat xs)%bool
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition missingNumber_precond_dec (nums : list nat) : bool :=
  let n := length nums in
  (all (fun x => Nat.leb x n) nums && nodup_nat nums)%bool.
(* !benchmark @end precond_aux *)

Definition missingNumber_precond (nums : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  missingNumber_precond_dec nums = true /\ NoDup nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code auxiliaries needed *)
(* !benchmark @end code_aux *)

Definition missingNumber (nums : (list nat)) (h_precond : missingNumber_precond nums) : nat :=
  (* !benchmark @start code *)
  let n := length nums in
let expectedSum := Nat.div (n * (n + 1)) 2 in
let actualSum := sum_nat nums in
Nat.sub expectedSum actualSum
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition missingNumber_postcond_dec (nums : list nat) (result : nat) : bool :=
  let n := length nums in
  let range_list := range n in
  (mem_nat result range_list && negb (mem_nat result nums))%bool.
(* !benchmark @end postcond_aux *)

Definition missingNumber_postcond (nums : (list nat)) (result : nat) (h_precond : missingNumber_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
In result (range n) /\ ~In result nums /\ (forall x, In x (range n) -> x <> result -> In x nums)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem missingNumber_postcond_satisfied (nums : (list nat)) (h_precond : missingNumber_precond nums) :
    missingNumber_postcond nums (missingNumber nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
