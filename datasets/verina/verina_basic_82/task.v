(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint copyFrom (a : list Z) (i : nat) (fuel : nat) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      match nth_error a i with
      | Some elem => copyFrom a (i + 1)%nat fuel' (acc ++ [elem])
      | None => acc
      end
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition remove_front_precond_dec (a : list Z) : bool :=
  (0 <? length a)%nat.
(* !benchmark @end precond_aux *)

Definition remove_front_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers needed *)
(* !benchmark @end code_aux *)

Definition remove_front (a : (list Z)) (h_precond : remove_front_precond a) : (list Z) :=
  (* !benchmark @start code *)
  match (0 <? length a)%nat with
  | true => copyFrom a 1%nat (length a) []
  | false => []
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition remove_front_postcond_dec (a : list Z) (result : list Z) : bool :=
  ((0 <? length a)%nat) &&
  (Nat.eqb (length result) (length a - 1)%nat) &&
  (forallb (fun i => 
    match nth_error result i, nth_error a (i + 1)%nat with
    | Some r, Some a_elem => Z.eqb r a_elem
    | _, _ => false
    end) (seq 0 (length result))).
(* !benchmark @end postcond_aux *)

Definition remove_front_postcond (a : (list Z)) (result : (list Z)) (h_precond : remove_front_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (length a > 0)%nat /\ 
  length result = (length a - 1)%nat /\ 
  (forall i : nat, (i < length result)%nat -> 
    nth_error result i = nth_error a (i + 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem remove_front_postcond_satisfied (a : (list Z)) (h_precond : remove_front_precond a) :
    remove_front_postcond a (remove_front a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
