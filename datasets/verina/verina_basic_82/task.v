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

Definition remove_front_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition remove_front_impl (a : list Z) : list Z :=
  match a with
  | [] => []
  | _ :: tl => tl
  end.
(* !benchmark @end code_aux *)

Definition remove_front (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  remove_front_impl a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n'
  end.

Fixpoint check_elements (result a : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' => ((nth_Z result i' =? nth_Z a (i' + 1)%nat)%Z) && check_elements result a i'
  end.
(* !benchmark @end postcond_aux *)

Definition remove_front_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  (1 <=? length a)%nat && ((length result =? (length a - 1)%nat)%nat) && check_elements result a (length result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem remove_front_postcond_satisfied (a : (list Z)) :
    remove_front_precond a = true ->
    remove_front_postcond a (remove_front a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
