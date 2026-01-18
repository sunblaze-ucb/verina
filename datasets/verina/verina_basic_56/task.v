(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition copy_precond_dec (src : list Z) (sStart : nat) (dest : list Z) (dStart : nat) (len : nat) : bool :=
  (sStart + len <=? length src)%nat && (dStart + len <=? length dest)%nat.
(* !benchmark @end precond_aux *)

Definition copy_precond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) : Prop :=
  (* !benchmark @start precond *)
  (length src >= sStart + len)%nat /\ (length dest >= dStart + len)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Fixpoint updateSegment (r : list Z) (src : list Z) (sStart : nat) (dStart : nat) (n : nat) : list Z :=
  match n with
  | O => r
  | S n' =>
      let idx_src := (sStart + n')%nat in
      let idx_dest := (dStart + n')%nat in
      let val := nth idx_src src 0%Z in
      let r_new := 
        (firstn idx_dest r) ++ [val] ++ (skipn (idx_dest + 1)%nat r)
      in
      updateSegment r_new src sStart dStart n'
  end.
(* !benchmark @end code_aux *)

Definition copy (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (h_precond : copy_precond src sStart dest dStart len) : (list Z) :=
  (* !benchmark @start code *)
  if Nat.eqb len 0%nat then dest
else updateSegment dest src sStart dStart len
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Definition copy_postcond_dec (src : list Z) (sStart : nat) (dest : list Z) (dStart : nat) (len : nat) (result : list Z) : bool :=
  (Nat.eqb (length result) (length dest)) &&
  (forallb (fun i => Z.eqb (nth i result 0%Z) (nth i dest 0%Z)) (seq 0%nat dStart)) &&
  (forallb (fun i => if (i <? length result)%nat then Z.eqb (nth i result 0%Z) (nth i dest 0%Z) else true) (seq (dStart + len)%nat (length dest - (dStart + len))%nat)) &&
  (forallb (fun i => Z.eqb (nth (dStart + i)%nat result 0%Z) (nth (sStart + i)%nat src 0%Z)) (seq 0%nat len)).
(* !benchmark @end postcond_aux *)

Definition copy_postcond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (result : (list Z)) (h_precond : copy_precond src sStart dest dStart len) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length dest)%nat /\
(forall i, (i < dStart)%nat -> nth i result 0%Z = nth i dest 0%Z) /\
(forall i, (dStart + len <= i)%nat -> (i < length result)%nat -> nth i result 0%Z = nth i dest 0%Z) /\
(forall i, (i < len)%nat -> nth (dStart + i) result 0%Z = nth (sStart + i) src 0%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem copy_postcond_satisfied (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (h_precond : copy_precond src sStart dest dStart len) :
    copy_postcond src sStart dest dStart len (copy src sStart dest dStart len h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
