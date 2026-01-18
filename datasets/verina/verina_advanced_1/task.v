(* !benchmark @start import type=task *)
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint count_in_list (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if (y =? x)%Z then S (count_in_list x ys) else count_in_list x ys
  end.

Fixpoint map_count (l : list Z) (original : list Z) : list nat :=
  match l with
  | [] => []
  | x :: xs => count_in_list x original :: map_count xs original
  end.

Fixpoint all_pred_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (f x) (all_pred_nat f xs)
  end.

Definition count_is_1_or_2 (n : nat) : bool :=
  orb (Nat.eqb n 1%nat) (Nat.eqb n 2%nat).

Fixpoint count_ones (l : list nat) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Nat.eqb x 1%nat then S (count_ones xs) else count_ones xs
  end.

Definition FindSingleNumber_precond_dec (nums : list Z) : bool :=
  let numsCount := map_count nums nums in
  andb (all_pred_nat count_is_1_or_2 numsCount) (Nat.eqb (count_ones numsCount) 1%nat).
(* !benchmark @end precond_aux *)

Definition FindSingleNumber_precond (nums : list Z) : Prop :=
  (* !benchmark @start precond *)
  let numsCount := map_count nums nums in
  (forall count, In count numsCount -> count = 1%nat \/ count = 2%nat) /\
  count_ones numsCount = 1%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint filterlist (x : Z) (nums : list Z) : list Z :=
  match nums with
  | [] => []
  | y :: ys => if (y =? x)%Z then y :: filterlist x ys else filterlist x ys
  end.

Fixpoint findUnique (remaining : list Z) (nums : list Z) : Z :=
  match remaining with
  | [] => 0
  | x :: xs =>
      let filtered := filterlist x nums in
      let count := length filtered in
      if Nat.eqb count 1%nat then x
      else findUnique xs nums
  end.
(* !benchmark @end code_aux *)

Definition FindSingleNumber (nums : list Z) (h_precond : FindSingleNumber_precond nums) : Z :=
  (* !benchmark @start code *)
  findUnique nums nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint length_nat {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0%nat
  | _ :: xs => S (length_nat xs)
  end.

Definition FindSingleNumber_postcond_dec (nums : list Z) (result : Z) : bool :=
  let len := length_nat nums in
  let filtered_result := filterlist result nums in
  let filtered_len := length_nat filtered_result in
  andb (andb (Nat.ltb 0 len) (Nat.eqb filtered_len 1%nat))
    (forallb (fun x => orb ((x =? result)%Z) (Nat.eqb (length_nat (filterlist x nums)) 2%nat)) nums).
(* !benchmark @end postcond_aux *)

Definition FindSingleNumber_postcond (nums : list Z) (result : Z) (h_precond : FindSingleNumber_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (length nums > 0)%nat /\
  length (filterlist result nums) = 1%nat /\
  (forall x : Z, In x nums ->
    x = result \/ length (filterlist x nums) = 2%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem FindSingleNumber_postcond_satisfied (nums : list Z) (h_precond : FindSingleNumber_precond nums) :
    FindSingleNumber_postcond nums (FindSingleNumber nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
