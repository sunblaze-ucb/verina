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

Definition arrayProduct_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (length a =? length b)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a b : list Z) (len : nat) (i : nat) (c : list Z) : list Z :=
  match len with
  | O => c
  | S len' =>
    let a_val := match nth_error a i with Some v => v | None => 0 end in
    let b_val := match nth_error b i with Some v => v | None => 0 end in
    let new_c := firstn i c ++ [a_val * b_val] ++ skipn (S i) c in
    loop a b len' (S i) new_c
  end.

Definition mkArray (n : nat) (v : Z) : list Z := repeat v n.
(* !benchmark @end code_aux *)

Definition arrayProduct (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let len := length a in
  let c := mkArray len 0 in
  loop a b len O c
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint check_all_indices (a b result : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' =>
    let a_val := match nth_error a i' with Some v => v | None => 0 end in
    let b_val := match nth_error b i' with Some v => v | None => 0 end in
    let r_val := match nth_error result i' with Some v => v | None => 0 end in
    ((a_val * b_val =? r_val)%Z && check_all_indices a b result i')%bool
  end.
(* !benchmark @end postcond_aux *)

Definition arrayProduct_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a)%nat && check_all_indices a b result (length a))%bool
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arrayProduct_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    arrayProduct_precond a b = true ->
    arrayProduct_postcond a b (arrayProduct a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
