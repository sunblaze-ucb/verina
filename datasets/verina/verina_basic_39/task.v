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

Definition rotateRight_precond (l : (list Z)) (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition getD (l : list Z) (idx : nat) (default : Z) : Z :=
  match nth_error l idx with
  | Some v => v
  | None => default
  end.

Definition headD (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: _ => h
  end.
(* !benchmark @end code_aux *)

Definition rotateRight (l : (list Z)) (n : nat) : (list Z) :=
  (* !benchmark @start code *)
  let len := length l in
    if (len =? 0)%nat then l
    else
      map (fun i : nat =>
        let idx_int : Z := ((Z.of_nat i - Z.of_nat n + Z.of_nat len) mod Z.of_nat len) in
        let idx_nat : nat := Z.to_nat idx_int in
        getD l idx_nat (headD l 0)
      ) (seq 0 len)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forall_nat_lt (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S k => f k && forall_nat_lt k f
  end.

Definition Z_eqb_option (o1 o2 : option Z) : bool :=
  match o1, o2 with
  | Some v1, Some v2 => (v1 =? v2)%Z
  | None, None => true
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition rotateRight_postcond (l : (list Z)) (n : nat) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  let len := length l in
  ((length result =? len)%nat &&
    forall_nat_lt len (fun i =>
      let rotated_index := Z.to_nat ((Z.of_nat i - Z.of_nat n + Z.of_nat len) mod Z.of_nat len) in
      Z_eqb_option (nth_error result i) (nth_error l rotated_index)
    ))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rotateRight_postcond_satisfied (l : (list Z)) (n : nat) :
    rotateRight_precond l n = true ->
    rotateRight_postcond l n (rotateRight l n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
