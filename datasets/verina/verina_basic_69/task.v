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
Fixpoint existsb_with_index_aux (a : list Z) (e : Z) (i : nat) : bool :=
  match a with
  | [] => false
  | h :: t => if (h =? e)%Z then true else existsb_with_index_aux t e (S i)
  end.
(* !benchmark @end precond_aux *)

Definition LinearSearch_precond (a : (list Z)) (e : Z) : bool :=
  (* !benchmark @start precond *)
  existsb_with_index_aux a e O
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint linearSearchAux (a : list Z) (e : Z) (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
    match nth_error a n with
    | Some v => if (v =? e)%Z then n else linearSearchAux a e (S n) fuel'
    | None => O
    end
  end.
(* !benchmark @end code_aux *)

Definition LinearSearch (a : (list Z)) (e : Z) : nat :=
  (* !benchmark @start code *)
  linearSearchAux a e O (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nth_Z (l : list Z) (n : nat) : Z :=
  match nth_error l n with
  | Some v => v
  | None => 0%Z
  end.

Fixpoint all_before_neq (a : list Z) (e : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => if (nth_Z a k' =? e)%Z then false else all_before_neq a e k'
  end.
(* !benchmark @end postcond_aux *)

Definition LinearSearch_postcond (a : (list Z)) (e : Z) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result <? length a)%nat && (nth_Z a result =? e)%Z && all_before_neq a e result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch_postcond_satisfied (a : (list Z)) (e : Z) :
    LinearSearch_precond a e = true ->
    LinearSearch_postcond a e (LinearSearch a e) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
