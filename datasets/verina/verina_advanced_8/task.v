(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition canCompleteCircuit_precond (gas : (list Z)) (cost : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length gas)%nat && (length gas =? length cost)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint walk (pairs : list (Z * Z)) (i : nat) (tank : Z) (start : nat) : Z :=
  match pairs with
  | [] => Z.of_nat start
  | (g, c) :: rest =>
    let newTank := tank + g - c in
    if newTank <? 0 then
      walk rest (S i) 0 (S i)
    else
      walk rest (S i) newTank start
  end.
(* !benchmark @end code_aux *)

Definition canCompleteCircuit (gas : (list Z)) (cost : (list Z)) : Z :=
  (* !benchmark @start code *)
  let totalGas := sum_list gas in
  let totalCost := sum_list cost in
  if totalGas <? totalCost then
    -1
  else
    walk (combine gas cost) 0%nat 0 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint foldl_nat {A : Type} (f : A -> nat -> A) (acc : A) (l : list nat) : A :=
  match l with
  | [] => acc
  | x :: xs => foldl_nat f (f acc x) xs
  end.

Definition compute_acc (gas cost : list Z) (start : nat) (i : nat) : Z :=
  let n := length gas in
  foldl_nat (fun t j =>
    let jdx := ((start + j) mod n)%nat in
    t + nth_Z gas jdx - nth_Z cost jdx
  ) 0 (range (S i)).

Definition valid (gas cost : list Z) (start : nat) : bool :=
  let n := length gas in
  forallb (fun i => (compute_acc gas cost start i >=? 0)) (range n).
(* !benchmark @end postcond_aux *)

Definition canCompleteCircuit_postcond (gas : (list Z)) (cost : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let valid_start := valid gas cost in
  implb (result =? -1) (forallb (fun s => negb (valid_start s)) (range (length gas))) &&
  implb (result >=? 0) (
    (result <? Z.of_nat (length gas)) &&
    valid_start (Z.to_nat result) &&
    forallb (fun s => negb (valid_start s)) (range (Z.to_nat result))
  )
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem canCompleteCircuit_postcond_satisfied (gas : (list Z)) (cost : (list Z)) :
    canCompleteCircuit_precond gas cost = true ->
    canCompleteCircuit_postcond gas cost (canCompleteCircuit gas cost) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
