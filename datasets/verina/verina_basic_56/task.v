(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Nat.
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

Definition copy_precond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) : bool :=
  (* !benchmark @start precond *)
  ((sStart + len <=? length src)%nat && (dStart + len <=? length dest)%nat)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | h :: _, O => h
  | _ :: t, S n' => nth_default_Z t n'
  end.

Fixpoint set_nth_Z (l : list Z) (n : nat) (v : Z) : list Z :=
  match l, n with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S n' => h :: set_nth_Z t n' v
  end.

Fixpoint updateSegment (r src : list Z) (sStart dStart n : nat) : list Z :=
  match n with
  | O => r
  | S n' =>
      let rNew := set_nth_Z r (dStart + n')%nat (nth_default_Z src (sStart + n')%nat) in
      updateSegment rNew src sStart dStart n'
  end.
(* !benchmark @end code_aux *)

Definition copy (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) : (list Z) :=
  (* !benchmark @start code *)
  if (len =? 0)%nat then dest
  else updateSegment dest src sStart dStart len
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z_post (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | h :: _, O => h
  | _ :: t, S n' => nth_default_Z_post t n'
  end.

Fixpoint forallb_nat (f : nat -> bool) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f n' && forallb_nat f n'
  end.
(* !benchmark @end postcond_aux *)

Definition copy_postcond (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length dest)%nat &&
   forallb_nat (fun i => implb (i <? dStart)%nat (nth_default_Z_post result i =? nth_default_Z_post dest i)) (length result) &&
   forallb_nat (fun i => implb ((dStart + len <=? i)%nat && (i <? length result)%nat) (nth_default_Z_post result i =? nth_default_Z_post dest i)) (length result) &&
   forallb_nat (fun i => (nth_default_Z_post result (dStart + i)%nat =? nth_default_Z_post src (sStart + i)%nat)) len)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem copy_postcond_satisfied (src : (list Z)) (sStart : nat) (dest : (list Z)) (dStart : nat) (len : nat) :
    copy_precond src sStart dest dStart len = true ->
    copy_postcond src sStart dest dStart len (copy src sStart dest dStart len) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
