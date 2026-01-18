(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No additional task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint all_binary (digits : list nat) : bool :=
  match digits with
  | [] => true
  | d :: rest => (Nat.eqb d 0%nat || Nat.eqb d 1%nat) && all_binary rest
  end.

Definition binaryToDecimal_precond_dec (digits : list nat) : bool :=
  all_binary digits.
(* !benchmark @end precond_aux *)

Definition binaryToDecimal_precond (digits : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  forall d, In d digits -> (d = 0%nat \/ d = 1%nat)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint binaryToDecimal_helper (digits : list nat) : nat :=
  match digits with
  | [] => 0%nat
  | first :: rest => (first * Nat.pow 2 (length rest) + binaryToDecimal_helper rest)%nat
  end.
(* !benchmark @end code_aux *)

Definition binaryToDecimal (digits : (list nat)) (h_precond : binaryToDecimal_precond digits) : nat :=
  (* !benchmark @start code *)
  binaryToDecimal_helper digits
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint foldl_binary (digits : list nat) : nat :=
  fold_left (fun acc bit => (acc * 2 + bit)%nat) digits 0%nat.

Definition binaryToDecimal_postcond_dec (digits : list nat) (result : nat) : bool :=
  let expected := foldl_binary digits in
  Nat.eqb (result - expected) 0%nat && Nat.eqb (expected - result) 0%nat.
(* !benchmark @end postcond_aux *)

Definition binaryToDecimal_postcond (digits : (list nat)) (result : nat) (h_precond : binaryToDecimal_precond digits) : Prop :=
  (* !benchmark @start postcond *)
  (result - fold_left (fun acc bit => (acc * 2 + bit)%nat) digits 0%nat = 0%nat /\
 fold_left (fun acc bit => (acc * 2 + bit)%nat) digits 0%nat - result = 0%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem binaryToDecimal_postcond_satisfied (digits : (list nat)) (h_precond : binaryToDecimal_precond digits) :
    binaryToDecimal_postcond digits (binaryToDecimal digits h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
