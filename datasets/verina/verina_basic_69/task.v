(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Require Import Recdef.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition LinearSearch_precond_dec (a : list Z) (e : Z) : bool :=
  existsb (fun x => Z.eqb x e) a.
(* !benchmark @end precond_aux *)

Definition LinearSearch_precond (a : (list Z)) (e : Z) : Prop :=
  (* !benchmark @start precond *)
  exists i, (i < length a)%nat /\ nth i a 0%Z = e
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Require Import Recdef.

Function linearSearchAux (a : list Z) (e : Z) (n : nat) {measure (fun n => length a - n)%nat n} : nat :=
  match (n <? length a)%nat with
  | true =>
      match nth_error a n with
      | Some x => if Z.eqb x e then n else linearSearchAux a e (n + 1)%nat
      | None => 0%nat
      end
  | false => 0%nat
  end.
Proof.
  intros. apply Nat.ltb_lt in teq. lia.
Defined.
(* !benchmark @end code_aux *)

Definition LinearSearch (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) : nat :=
  (* !benchmark @start code *)
  linearSearchAux a e 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LinearSearch_postcond_dec (a : list Z) (e : Z) (result : nat) : bool :=
  ((result <? length a)%nat) &&
  (Z.eqb (nth result a 0%Z) e) &&
  (forallb (fun k => negb (Z.eqb (nth k a 0%Z) e)) (seq 0 result)).
(* !benchmark @end postcond_aux *)

Definition LinearSearch_postcond (a : (list Z)) (e : Z) (result : nat) (h_precond : LinearSearch_precond a e) : Prop :=
  (* !benchmark @start postcond *)
  (result < length a)%nat /\ 
nth result a 0%Z = e /\ 
(forall k : nat, (k < result)%nat -> nth k a 0%Z <> e)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch_postcond_satisfied (a : (list Z)) (e : Z) (h_precond : LinearSearch_precond a e) :
    LinearSearch_postcond a e (LinearSearch a e h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
