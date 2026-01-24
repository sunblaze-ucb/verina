(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
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

Definition TestArrayElements_precond (a : (list Z)) (j : nat) : bool :=
  (* !benchmark @start precond *)
  (j <? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match l with
  | [] => []
  | h :: t =>
    match n with
    | O => v :: t
    | S n' => h :: set_nth t n' v
    end
  end.
(* !benchmark @end code_aux *)

Definition TestArrayElements (a : (list Z)) (j : nat) : (list Z) :=
  (* !benchmark @start code *)
  set_nth a j 60
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_default_Z (l : list Z) (n : nat) (d : Z) : Z :=
  nth n l d.

Fixpoint forall_nat_below (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => f n' && forall_nat_below n' f
  end.
(* !benchmark @end postcond_aux *)

Definition TestArrayElements_postcond (a : (list Z)) (j : nat) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((nth_default_Z result j 0 =? 60)%Z) &&
  forall_nat_below (length a) (fun k =>
    implb (negb (k =? j)%nat) ((nth_default_Z result k 0 =? nth_default_Z a k 0)%Z)
  )
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem TestArrayElements_postcond_satisfied (a : (list Z)) (j : nat) :
    TestArrayElements_precond a j = true ->
    TestArrayElements_postcond a j (TestArrayElements a j) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
