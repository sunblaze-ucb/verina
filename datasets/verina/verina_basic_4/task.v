(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition kthElement_precond (arr : (list Z)) (k : nat) : bool :=
  (* !benchmark @start precond *)
  (1 <=? k)%nat && (k <=? length arr)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default (l : list Z) (n : nat) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default t n' default
              end
  end.
(* !benchmark @end code_aux *)

Definition kthElement (arr : (list Z)) (k : nat) : Z :=
  (* !benchmark @start code *)
  nth_default arr (k - 1)%nat 0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint any_Z (l : list Z) (f : Z -> bool) : bool :=
  match l with
  | [] => false
  | h :: t => f h || any_Z t f
  end.

Definition nth_default_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match nth_error l n with
  | Some v => v
  | None => default
  end.
(* !benchmark @end postcond_aux *)

Definition kthElement_postcond (arr : (list Z)) (k : nat) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  any_Z arr (fun x => andb (x =? result) (x =? nth_default_Z arr (k - 1)%nat 0%Z))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem kthElement_postcond_satisfied (arr : (list Z)) (k : nat) :
    kthElement_precond arr k = true ->
    kthElement_postcond arr k (kthElement arr k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
