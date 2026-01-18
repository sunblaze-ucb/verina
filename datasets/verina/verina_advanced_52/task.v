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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Fixpoint range_helper (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => acc
  | S n' => range_helper n' (n' :: acc)
  end.

Definition range (n : nat) : list nat := range_helper n [].

Fixpoint map_add_one (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => (h + 1)%nat :: map_add_one t
  end.

Fixpoint elem {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t => if eq_dec a h then true else elem eq_dec a t
  end.

Fixpoint all {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | h :: t => andb (f h) (all f t)
  end.

Definition minOperations_precond_dec (nums : list nat) (k : nat) : bool :=
  let target_nums := map_add_one (range k) in
  all (fun n => elem Nat.eq_dec n nums) target_nums.
(* !benchmark @end precond_aux *)

Definition minOperations_precond (nums : (list nat)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  let target_nums := map_add_one (range k) in
  all (fun n => elem Nat.eq_dec n nums) target_nums = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Fixpoint loop (remaining : list nat) (collected : list nat) (collected_count : nat) (ops : nat) (k : nat) : nat :=
  match remaining with
  | [] => ops
  | head :: tail =>
      let ops' := ops + 1 in
      if (head >? 0)%nat && (head <=? k)%nat && negb (elem Nat.eq_dec head collected) then
        let collected' := head :: collected in
        let collected_count' := collected_count + 1 in
        if Nat.eqb collected_count' k then
          ops'
        else
          loop tail collected' collected_count' ops' k
      else
        loop tail collected collected_count ops' k
  end.
(* !benchmark @end code_aux *)

Definition minOperations (nums : (list nat)) (k : nat) (h_precond : minOperations_precond nums k) : nat :=
  (* !benchmark @start code *)
  if Nat.eqb k 0%nat then 0%nat else loop (rev nums) [] 0%nat 0%nat k
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | S n', h :: t => h :: take n' t
  | _, [] => []
  end.

Definition minOperations_postcond_dec (nums : list nat) (k : nat) (result : nat) : bool :=
  let processed := take result (rev nums) in
  let target_nums := map_add_one (range k) in
  let collected_all := all (fun n => elem Nat.eq_dec n processed) target_nums in
  let is_minimal :=
    if (result >? 0)%nat then
      let processed_minus_one := take (result - 1) (rev nums) in
      negb (all (fun n => elem Nat.eq_dec n processed_minus_one) target_nums)
    else
      Nat.eqb k 0%nat
  in
  andb collected_all is_minimal.
(* !benchmark @end postcond_aux *)

Definition minOperations_postcond (nums : (list nat)) (k : nat) (result : nat) (h_precond : minOperations_precond nums k) : Prop :=
  (* !benchmark @start postcond *)
  let processed := take result (rev nums) in
  let target_nums := map_add_one (range k) in
  let collected_all := all (fun n => elem Nat.eq_dec n processed) target_nums in
  let is_minimal :=
    if (result >? 0)%nat then
      let processed_minus_one := take (result - 1) (rev nums) in
      negb (all (fun n => elem Nat.eq_dec n processed_minus_one) target_nums) = true
    else
      Nat.eqb k 0%nat = true
  in
  collected_all = true /\ is_minimal
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minOperations_postcond_satisfied (nums : (list nat)) (k : nat) (h_precond : minOperations_precond nums k) :
    minOperations_postcond nums k (minOperations nums k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
