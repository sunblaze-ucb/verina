(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import List.
Require Import Lia.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | [] => None
  | [x] => Some x
  | x :: xs =>
      match list_min xs with
      | None => Some x
      | Some m => Some (min x m)
      end
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition findSmallest_precond_dec (s : list nat) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition findSmallest_precond (s : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition findSmallest (s : (list nat)) (h_precond : findSmallest_precond s) : (option nat) :=
  (* !benchmark @start code *)
  list_min s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_minimum (r : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | _ => (existsb (Nat.eqb r) xs) && (forallb (fun x => (r <=? x)%nat) xs)
  end.

Definition findSmallest_postcond_dec (s : list nat) (result : option nat) : bool :=
  let xs := s in
  match result with
  | None => match xs with [] => true | _ => false end
  | Some r => is_minimum r xs
  end.
(* !benchmark @end postcond_aux *)

Definition findSmallest_postcond (s : (list nat)) (result : (option nat)) (h_precond : findSmallest_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let xs := s in
  match result with
  | None => xs = []
  | Some r => In r xs /\ (forall x, In x xs -> (r <= x)%nat)
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findSmallest_postcond_satisfied (s : (list nat)) (h_precond : findSmallest_precond s) :
    findSmallest_postcond s (findSmallest s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
