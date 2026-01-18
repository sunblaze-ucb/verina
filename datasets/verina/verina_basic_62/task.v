(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
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
Definition Find_precond_dec (a : list Z) (key : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition Find_precond (a : (list Z)) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint search (a : list Z) (key : Z) (index : nat) : Z :=
  match index with
  | O => match a with
         | [] => (-1)
         | hd :: tl => if (hd =? key)%Z then 0 else (1 + search tl key 0%nat)%Z
         end
  | S n => match a with
           | [] => (-1)
           | hd :: tl => search tl key n
           end
  end.

Fixpoint search_iter (a : list Z) (key : Z) (index : nat) (max : nat) : Z :=
  match max with
  | O => (-1)
  | S max' =>
      match nth_error a index with
      | Some v => if (v =? key)%Z then Z.of_nat index else search_iter a key (S index) max'
      | None => (-1)
      end
  end.
(* !benchmark @end code_aux *)

Definition Find (a : (list Z)) (key : Z) (h_precond : Find_precond a key) : Z :=
  (* !benchmark @start code *)
  search_iter a key 0%nat (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint all_not_key (a : list Z) (key : Z) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' => match nth_error a n' with
            | Some v => v <> key /\ all_not_key a key n'
            | None => all_not_key a key n'
            end
  end.

Definition Find_postcond_dec (a : list Z) (key : Z) (result : Z) : bool :=
  let len := Z.of_nat (length a) in
  let result_valid := orb (result =? (-1))%Z (andb (result >=? 0)%Z (result <? len)%Z) in
  let key_found := if (result =? (-1))%Z then true
                   else match nth_error a (Z.to_nat result) with
                        | Some v => (v =? key)%Z
                        | None => false
                        end in
  andb result_valid key_found.
(* !benchmark @end postcond_aux *)

Definition Find_postcond (a : (list Z)) (key : Z) (result : Z) (h_precond : Find_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  (result = (-1) \/ (result >= 0 /\ result < Z.of_nat (length a))) /\
((result <> (-1)) -> 
  (exists v, nth_error a (Z.to_nat result) = Some v /\ v = key) /\
  (forall i : nat, (i < Z.to_nat result)%nat -> 
    exists v, nth_error a i = Some v /\ v <> key)) /\
((result = (-1)) -> 
  forall i : nat, (i < length a)%nat -> 
    exists v, nth_error a i = Some v /\ v <> key)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Find_postcond_satisfied (a : (list Z)) (key : Z) (h_precond : Find_precond a key) :
    Find_postcond a key (Find a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
