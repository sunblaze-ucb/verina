(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition append_precond (a : (list Z)) (b : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint copy (a : list Z) (i : nat) (acc : list Z) : list Z :=
  match a with
  | [] => acc
  | h :: t => 
    if (i <? length a)%nat then
      copy t (i + 1)%nat (acc ++ [nth i a 0%Z])
    else
      acc
  end.
(* !benchmark @end code_aux *)

Definition append (a : (list Z)) (b : Z) : (list Z) :=
  (* !benchmark @start code *)
  let c_initial := a in
  let c_full := c_initial ++ [b] in
  c_full
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range_nat (start : nat) (len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: range_nat (S start) len'
  end.

Definition nth_Z (l : list Z) (i : nat) (default : Z) : Z :=
  nth i l default.
(* !benchmark @end postcond_aux *)

Definition append_postcond (a : (list Z)) (b : Z) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  forallb (fun i => (nth_Z result i 0%Z =? nth_Z a i 0%Z)%Z) (range_nat 0 (length a)) &&
  (nth_Z result (length a) 0%Z =? b)%Z &&
  (length result =? (length a + 1)%nat)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem append_postcond_satisfied (a : (list Z)) (b : Z) :
    append_precond a b = true ->
    append_postcond a b (append a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
