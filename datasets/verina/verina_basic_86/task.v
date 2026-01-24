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

Definition rotate_precond (a : (list Z)) (offset : Z) : bool :=
  (* !benchmark @start precond *)
  (offset >=? 0)%Z
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint rotateAux (a : list Z) (offset : Z) (i : nat) (len : nat) (b : list Z) : list Z :=
  match i with
  | O => b
  | S i' =>
    let current_idx := (len - i)%nat in
    let idx_int := (Z.of_nat current_idx + offset) mod (Z.of_nat len) in
    let idx_int_adjusted := if (idx_int <? 0)%Z then idx_int + Z.of_nat len else idx_int in
    let idx_nat := Z.to_nat idx_int_adjusted in
    let val := nth idx_nat a 0%Z in
    let new_b := firstn current_idx b ++ [val] ++ skipn (current_idx + 1)%nat b in
    rotateAux a offset i' len new_b
  end.

Definition rotate_impl (a : list Z) (offset : Z) : list Z :=
  let len := length a in
  match len with
  | O => []
  | _ =>
    let default_val := nth O a 0%Z in
    let b0 := repeat default_val len in
    rotateAux a offset len len b0
  end.
(* !benchmark @end code_aux *)

Definition rotate (a : (list Z)) (offset : Z) : (list Z) :=
  (* !benchmark @start code *)
  rotate_impl a offset
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint check_rotation (a result : list Z) (offset : Z) (i : nat) (len : nat) : bool :=
  match i with
  | O => true
  | S i' =>
    let current_idx := (len - i)%nat in
    let idx_int := (Z.of_nat current_idx + offset) mod (Z.of_nat len) in
    let idx_int_adjusted := if (idx_int <? 0)%Z then idx_int + Z.of_nat len else idx_int in
    let idx_nat := Z.to_nat idx_int_adjusted in
    let expected := nth idx_nat a 0%Z in
    let actual := nth current_idx result 0%Z in
    ((expected =? actual)%Z && check_rotation a result offset i' len)%bool
  end.
(* !benchmark @end postcond_aux *)

Definition rotate_postcond (a : (list Z)) (offset : Z) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length a)%nat &&
    (match length a with
     | O => true
     | _ => check_rotation a result offset (length a) (length a)
     end))%bool
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rotate_postcond_satisfied (a : (list Z)) (offset : Z) :
    rotate_precond a offset = true ->
    rotate_postcond a offset (rotate a offset) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
