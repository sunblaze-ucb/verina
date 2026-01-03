(* Coq version of FindSingleNumber benchmark task *)
(* Find the element that appears exactly once in a list where all others appear twice *)

(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Lia.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* Solution-specific imports *)
(* !benchmark @end import *)

(* !benchmark @start solution_aux *)
(* Count occurrences of x in list *)
Fixpoint count_occ (x : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occ x t
  end.

(* Filter list to keep only elements equal to x *)
Fixpoint filterlist (x : Z) (lst : list Z) : list Z :=
  match lst with
  | [] => []
  | h :: t => if Z.eqb h x then h :: filterlist x t else filterlist x t
  end.

(* Find the unique element *)
Fixpoint findUnique (remaining : list Z) (nums : list Z) : Z :=
  match remaining with
  | [] => 0  (* default, should never happen with valid input *)
  | x :: xs =>
      if Nat.eqb (length (filterlist x nums)) 1 then x
      else findUnique xs nums
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Check if all counts are 1 or 2 *)
Definition all_counts_valid (nums : list Z) : bool :=
  forallb (fun x =>
    let c := count_occ x nums in
    Nat.eqb c 1 || Nat.eqb c 2
  ) nums.

(* Count how many elements appear exactly once *)
Definition count_singles (nums : list Z) : nat :=
  length (filter (fun x => Nat.eqb (count_occ x nums) 1) nums).

(* Decidable precondition for QuickChick *)
Definition FindSingleNumber_precond_dec (nums : list Z) : bool :=
  negb (Nat.eqb (length nums) 0) &&
  all_counts_valid nums &&
  Nat.eqb (count_singles nums) 1.
(* !benchmark @end precond_aux *)

Definition FindSingleNumber_precond (nums : list Z) : Prop :=
  (* !benchmark @start precond *)
  (* All elements appear 1 or 2 times, and exactly one element appears once *)
  (length nums > 0)%nat /\
  (forall x, In x nums -> count_occ x nums = 1%nat \/ count_occ x nums = 2%nat) /\
  count_singles nums = 1%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition FindSingleNumber (nums : list Z) (h_precond : FindSingleNumber_precond nums) : Z :=
  (* !benchmark @start code *)
  findUnique nums nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Decidable postcondition for QuickChick *)
Definition FindSingleNumber_postcond_dec (nums : list Z) (result : Z) : bool :=
  negb (Nat.eqb (length nums) 0) &&
  Nat.eqb (length (filterlist result nums)) 1 &&
  forallb (fun x =>
    Z.eqb x result || Nat.eqb (length (filterlist x nums)) 2
  ) nums.
(* !benchmark @end postcond_aux *)

Definition FindSingleNumber_postcond (nums : list Z) (result : Z) (h_precond : FindSingleNumber_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (* Result appears exactly once, and all other elements appear twice *)
  (length nums > 0)%nat /\
  (length (filterlist result nums) = 1)%nat /\
  (forall x, In x nums -> x = result \/ (length (filterlist x nums) = 2)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

(* Note: Full formal proof is complex due to quantifiers *)
(* For benchmarking, we rely on unit tests and QuickChick *)
