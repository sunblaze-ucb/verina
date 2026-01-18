(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Fixpoint all_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (f x) (all_nat f xs)
  end.

Definition solution_precond_dec (nums : list nat) : bool :=
  let n := length nums in
  andb (andb (1 <=? n)%nat (n <=? 100)%nat)
       (all_nat (fun x => andb (1 <=? x)%nat (x <=? 100)%nat) nums).
(* !benchmark @end precond_aux *)

Definition solution_precond (nums : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  (1 <= length nums)%nat /\ (length nums <= 100)%nat /\ 
forall x, In x nums -> (1 <= x)%nat /\ (x <= 100)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | S n', [] => []
  | S n', _ :: xs => drop n' xs
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => []
  | S n', [] => []
  | S n', x :: xs => x :: take n' xs
  end.

Fixpoint range_helper (start len : nat) : list nat :=
  match len with
  | 0 => []
  | S len' => start :: range_helper (S start) len'
  end.

Definition range (n : nat) : list nat := range_helper 0 n.

Fixpoint elem (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => if Nat.eqb x y then true else elem x ys
  end.

Fixpoint remove_duplicates (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => 
      let rest := remove_duplicates xs in
      if elem x rest then rest else x :: rest
  end.

Definition subarray (nums : list nat) (i j : nat) : list nat :=
  take (j - i + 1) (drop i nums).

Definition distinctCount (l : list nat) : nat :=
  length (remove_duplicates l).

Fixpoint foldl_nat_nat (f : nat -> nat -> nat) (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => foldl_nat_nat f (f acc x) xs
  end.
(* !benchmark @end code_aux *)

Definition solution (nums : (list nat)) (h_precond : solution_precond nums) : nat :=
  (* !benchmark @start code *)
  let n := length nums in
foldl_nat_nat (fun acc i =>
  acc + foldl_nat_nat (fun acc' d =>
    let subarr := subarray nums i (i + d) in
    let cnt := distinctCount subarr in
    acc' + cnt * cnt
  ) 0 (range (n - i))
) 0 (range n)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Definition square_local (n : nat) : nat := n * n.

Definition solution_postcond_dec (nums : list nat) (result : nat) : bool :=
  let n := length nums in
  let expectedSum :=
    foldl_nat_nat (fun outerSum i =>
      let innerSum :=
        foldl_nat_nat (fun currentInnerSum d =>
          let j := i + d in
          let subarr := subarray nums i j in
          let count := distinctCount subarr in
          currentInnerSum + square_local count
        ) 0 (range (n - i))
      in
      outerSum + innerSum
    ) 0 (range n)
  in
  Nat.eqb result expectedSum.
(* !benchmark @end postcond_aux *)

Definition solution_postcond (nums : (list nat)) (result : nat) (h_precond : solution_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
let getSubarray_local := fun (i j : nat) => subarray nums i j in
let distinctCount_local := fun (l : list nat) => distinctCount l in
let square_local := fun (n : nat) => n * n in
(1 <= n)%nat /\ (n <= 100)%nat /\ 
(forall x, In x nums -> (1 <= x)%nat /\ (x <= 100)%nat) ->
(result >= 0)%nat /\
(let expectedSum :=
  foldl_nat_nat (fun outerSum i =>
    let innerSum :=
      foldl_nat_nat (fun currentInnerSum d =>
        let j := i + d in
        let subarr := getSubarray_local i j in
        let count := distinctCount_local subarr in
        currentInnerSum + square_local count
      ) 0 (range (n - i))
    in
    outerSum + innerSum
  ) 0 (range n)
in
result = expectedSum)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem solution_postcond_satisfied (nums : (list nat)) (h_precond : solution_precond nums) :
    solution_postcond nums (solution nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
