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
(* Helper to count occurrences of x in list *)
Fixpoint count_Z (x : Z) (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | h :: t => if (h =? x)%Z then S (count_Z x t) else count_Z x t
  end.

(* Check if any element appears more than n/2 times *)
Fixpoint any_majority (xs : list Z) (n : nat) : bool :=
  match xs with
  | [] => false
  | h :: t => if (count_Z h xs >? n / 2)%nat then true else any_majority t n
  end.

Definition majorityElement_precond_dec (nums : list Z) : bool :=
  ((length nums >? 0)%nat && any_majority nums (length nums))%bool.
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  ((length nums > 0)%nat /\ exists x, In x nums /\ (count_Z x nums > length nums / 2)%nat)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => [x]
  | h :: t =>
    if (x <=? h)%Z then
      x :: h :: t
    else
      h :: insert x t
  end.

Fixpoint insertionSort (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | h :: t =>
    let sortedTail := insertionSort t in
    let sorted := insert h sortedTail in
    sorted
  end.

Definition getAt (xs : list Z) (i : nat) : Z :=
  match skipn i xs with
  | [] => 0%Z
  | h :: _ => h
  end.
(* !benchmark @end code_aux *)

Definition majorityElement (nums : (list Z)) (h_precond : majorityElement_precond nums) : Z :=
  (* !benchmark @start code *)
  let sorted := insertionSort nums in
  let len := length sorted in
  let mid := (len / 2)%nat in
  getAt sorted mid
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_majority (result : Z) (xs : list Z) (n : nat) : bool :=
  match xs with
  | [] => true
  | h :: t => if (h =? result)%Z then all_majority result t n
              else if (count_Z h xs <=? n / 2)%nat then all_majority result t n
              else false
  end.

Definition majorityElement_postcond_dec (nums : list Z) (result : Z) : bool :=
  let n := length nums in
  ((count_Z result nums >? n / 2)%nat && all_majority result nums n)%bool.
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (nums : (list Z)) (result : Z) (h_precond : majorityElement_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
  (count_Z result nums > n / 2)%nat /\
  (forall x, In x nums -> (x = result \/ (count_Z x nums <= n / 2)%nat))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (nums : (list Z)) (h_precond : majorityElement_precond nums) :
    majorityElement_postcond nums (majorityElement nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
