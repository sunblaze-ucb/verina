(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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
Definition kthElement_precond_dec (arr : list Z) (k : nat) : bool :=
  (1 <=? k)%nat && (k <=? length arr)%nat.
(* !benchmark @end precond_aux *)

Definition kthElement_precond (arr : (list Z)) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  (k >= 1)%nat /\ (k <= length arr)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
(* !benchmark @end code_aux *)

Definition kthElement (arr : (list Z)) (k : nat) (h_precond : kthElement_precond arr k) : Z :=
  (* !benchmark @start code *)
  match nth_error arr (k - 1) with
| Some x => x
| None => 0
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition kthElement_postcond_dec (arr : list Z) (k : nat) (result : Z) : bool :=
  match nth_error arr (k - 1) with
  | Some x => existsb (fun elem => (elem =? result) && (elem =? x)) arr
  | None => false
  end.
(* !benchmark @end postcond_aux *)

Definition kthElement_postcond (arr : (list Z)) (k : nat) (result : Z) (h_precond : kthElement_precond arr k) : Prop :=
  (* !benchmark @start postcond *)
  exists x : Z, In x arr /\ x = result /\ match nth_error arr (k - 1) with
                                         | Some y => x = y
                                         | None => False
                                         end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem kthElement_postcond_satisfied (arr : (list Z)) (k : nat) (h_precond : kthElement_precond arr k) :
    kthElement_postcond arr k (kthElement arr k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
