(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint existsb_with_index {A : Type} (f : nat -> A -> bool) (l : list A) (start : nat) : bool :=
  match l with
  | [] => false
  | h :: t => if f start h then true else existsb_with_index f t (S start)
  end.
(* !benchmark @end precond_aux *)

Definition LinearSearch3_precond (a : (list Z)) (P : (Z -> bool)) : bool :=
  (* !benchmark @start precond *)
  existsb_with_index (fun i x => P x) a O
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a : list Z) (P : Z -> bool) (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
    if (n <? length a)%nat then
      match nth_error a n with
      | Some v => if P v then n else loop a P (S n) fuel'
      | None => O
      end
    else O
  end.
(* !benchmark @end code_aux *)

Definition LinearSearch3 (a : (list Z)) (P : (Z -> bool)) : nat :=
  (* !benchmark @start code *)
  loop a P O (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_default (l : list Z) (n : nat) (d : Z) : Z :=
  match nth_error l n with
  | Some v => v
  | None => d
  end.

Fixpoint forallb_below (P : Z -> bool) (a : list Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => forallb_below P a k' && negb (P (nth_default a k' 0%Z))
  end.
(* !benchmark @end postcond_aux *)

Definition LinearSearch3_postcond (a : (list Z)) (P : (Z -> bool)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result <? length a)%nat && P (nth_default a result 0%Z) && forallb_below P a result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch3_postcond_satisfied (a : (list Z)) (P : (Z -> bool)) :
    LinearSearch3_precond a P = true ->
    LinearSearch3_postcond a P (LinearSearch3 a P) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
