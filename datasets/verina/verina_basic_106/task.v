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

Definition arraySum_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (length a =? length b)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint arraySum_loop (a b : list Z) : list Z :=
  match a, b with
  | [], [] => []
  | ha :: ta, hb :: tb => (ha + hb) :: arraySum_loop ta tb
  | _, _ => []
  end.
(* !benchmark @end code_aux *)

Definition arraySum (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  arraySum_loop a b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | h :: t, O => h
  | h :: t, S n' => nth_Z t n' default
  end.

Fixpoint check_all_indices (a b result : list Z) (i n : nat) : bool :=
  match n with
  | O => true
  | S n' => 
    let ai := nth_Z a i 0 in
    let bi := nth_Z b i 0 in
    let ri := nth_Z result i 0 in
    ((ai + bi =? ri) && check_all_indices a b result (S i) n')%bool
  end.
(* !benchmark @end postcond_aux *)

Definition arraySum_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a)%nat && check_all_indices a b result O (length a))%bool
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arraySum_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    arraySum_precond a b = true ->
    arraySum_postcond a b (arraySum a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
