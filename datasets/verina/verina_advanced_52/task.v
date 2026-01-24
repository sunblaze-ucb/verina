(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint elem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? n)%nat then true else elem_nat n t
  end.
(* !benchmark @end precond_aux *)

Definition minOperations_precond (nums : (list nat)) (k : nat) : bool :=
  (* !benchmark @start precond *)
  let target_nums := map (fun x => x + 1)%nat (seq 0 k) in
  forallb (fun n => elem_nat n nums) target_nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint elem_nat_code (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? n)%nat then true else elem_nat_code n t
  end.

Fixpoint loop (remaining : list nat) (collected : list nat) (collected_count : nat) (ops : nat) (k : nat) : nat :=
  match remaining with
  | [] => ops
  | head :: tail =>
    let ops' := (ops + 1)%nat in
    if (1 <=? head)%nat && (head <=? k)%nat && negb (elem_nat_code head collected) then
      let collected' := head :: collected in
      let collected_count' := (collected_count + 1)%nat in
      if (collected_count' =? k)%nat then ops'
      else loop tail collected' collected_count' ops' k
    else
      loop tail collected collected_count ops' k
  end.
(* !benchmark @end code_aux *)

Definition minOperations (nums : (list nat)) (k : nat) : nat :=
  (* !benchmark @start code *)
  if (k =? 0)%nat then 0%nat
  else loop (rev nums) [] 0%nat 0%nat k
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint elem_nat_post (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? n)%nat then true else elem_nat_post n t
  end.
(* !benchmark @end postcond_aux *)

Definition minOperations_postcond (nums : (list nat)) (k : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let processed := firstn result (rev nums) in
  let target_nums := map (fun x => (x + 1)%nat) (seq 0 k) in
  let collected_all := forallb (fun n => elem_nat_post n processed) target_nums in
  let is_minimal :=
    if (1 <=? result)%nat then
      let processed_minus_one := firstn (result - 1)%nat (rev nums) in
      negb (forallb (fun n => elem_nat_post n processed_minus_one) target_nums)
    else
      (k =? 0)%nat
  in
  collected_all && is_minimal
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minOperations_postcond_satisfied (nums : (list nat)) (k : nat) :
    minOperations_precond nums k = true ->
    minOperations_postcond nums k (minOperations nums k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
