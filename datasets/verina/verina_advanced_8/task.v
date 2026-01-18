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
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition canCompleteCircuit_precond_dec (gas : list Z) (cost : list Z) : bool :=
  (Nat.ltb 0 (length gas) && Nat.eqb (length gas) (length cost))%bool.
(* !benchmark @end precond_aux *)

Definition canCompleteCircuit_precond (gas : (list Z)) (cost : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  ((length gas > 0)%nat /\ length gas = length cost)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Fixpoint fold_left_Z (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => fold_left_Z xs (acc + x)
  end.

Fixpoint walk (pairs : list (Z * Z)) (i : nat) (tank : Z) (start : nat) : Z :=
  match pairs with
  | [] => Z.of_nat start
  | (g, c) :: rest =>
      let newTank := (tank + g - c)%Z in
      if (newTank <? 0)%Z then
        walk rest (i + 1)%nat 0 (i + 1)%nat
      else
        walk rest (i + 1)%nat newTank start
  end.
(* !benchmark @end code_aux *)

Definition canCompleteCircuit (gas : (list Z)) (cost : (list Z)) (h_precond : canCompleteCircuit_precond gas cost) : Z :=
  (* !benchmark @start code *)
  let totalGas := fold_left_Z gas 0 in
  let totalCost := fold_left_Z cost 0 in
  if (totalGas <? totalCost)%Z then
    (-1)%Z
  else
    let zipped := combine gas cost in
    walk zipped 0%nat 0 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint nth_default_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: xs => match n with
               | O => x
               | S n' => nth_default_Z xs n' default
               end
  end.

Fixpoint seq (start : nat) (len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: seq (S start) len'
  end.

Fixpoint allb_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => (f x && allb_nat f xs)%bool
  end.

Fixpoint fold_left_nat_Z (f : Z -> nat -> Z) (l : list nat) (acc : Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => fold_left_nat_Z f xs (f acc x)
  end.

Definition valid_start (gas cost : list Z) (start : nat) : bool :=
  allb_nat (fun i =>
    let acc := fold_left_nat_Z (fun t j =>
      let jdx := ((start + j) mod (length gas))%nat in
      (t + nth_default_Z gas jdx 0 - nth_default_Z cost jdx 0)%Z)
      (seq 0%nat (S i)) 0 in
    (acc >=? 0)%Z)
    (seq 0%nat (length gas)).

Definition canCompleteCircuit_postcond_dec (gas : list Z) (cost : list Z) (result : Z) : bool :=
  if (result =? -1)%Z then
    allb_nat (fun start => negb (valid_start gas cost start)) (seq 0%nat (length gas))
  else
    ((result >=? 0)%Z && Nat.ltb (Z.to_nat result) (length gas) && 
     valid_start gas cost (Z.to_nat result) &&
     allb_nat (fun start => negb (valid_start gas cost start)) (seq 0%nat (Z.to_nat result)))%bool.

Definition valid (gas cost : list Z) (start : nat) : Prop :=
  forall i, (i < length gas)%nat ->
    let acc := fold_left (fun t j =>
      let jdx := ((start + j) mod (length gas))%nat in
      (t + nth_default_Z gas jdx 0 - nth_default_Z cost jdx 0)%Z)
      (seq 0%nat (S i)) 0 in
    (acc >= 0)%Z.
(* !benchmark @end postcond_aux *)

Definition canCompleteCircuit_postcond (gas : (list Z)) (cost : (list Z)) (result : Z) (h_precond : canCompleteCircuit_precond gas cost) : Prop :=
  (* !benchmark @start postcond *)
  let result_val := result in
  ((result_val = -1)%Z -> forall start, (start < length gas)%nat -> ~ valid gas cost start) /\
  ((result_val >= 0)%Z -> 
    (Z.to_nat result_val < length gas)%nat /\ 
    valid gas cost (Z.to_nat result_val) /\
    forall start, (start < Z.to_nat result_val)%nat -> ~ valid gas cost start)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem canCompleteCircuit_postcond_satisfied (gas : (list Z)) (cost : (list Z)) (h_precond : canCompleteCircuit_precond gas cost) :
    canCompleteCircuit_postcond gas cost (canCompleteCircuit gas cost h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
