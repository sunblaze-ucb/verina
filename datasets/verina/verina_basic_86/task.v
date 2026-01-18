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
Definition rotate_precond_dec (a : list Z) (offset : Z) : bool :=
  (offset >=? 0)%Z.
(* !benchmark @end precond_aux *)

Definition rotate_precond (a : (list Z)) (offset : Z) : Prop :=
  (* !benchmark @start precond *)
  (offset >= 0)%Z
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint rotateAux (a : list Z) (offset : Z) (len : nat) (b : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => b
  | S fuel' =>
      let i := (len - S fuel')%nat in
      if Nat.ltb i len then
        let idx_int := ((Z.of_nat i) + offset)%Z in
        let len_z := Z.of_nat len in
        let idx_mod := (idx_int mod len_z)%Z in
        let idx_adjusted := if (idx_mod <? 0)%Z then (idx_mod + len_z)%Z else idx_mod in
        let idx_nat := Z.to_nat idx_adjusted in
        let new_b := 
          match nth_error a idx_nat with
          | Some v => 
              match nth_error b i with
              | Some _ => 
                  (firstn i b) ++ [v] ++ (skipn (S i) b)
              | None => b
              end
          | None => b
          end in
        rotateAux a offset len new_b fuel'
      else b
  end.
(* !benchmark @end code_aux *)

Definition rotate (a : (list Z)) (offset : Z) (h_precond : rotate_precond a offset) : (list Z) :=
  (* !benchmark @start code *)
  let len := length a in
let default_val := match a with
                   | [] => 0%Z
                   | h :: _ => h
                   end in
let b0 := repeat default_val len in
rotateAux a offset len b0 len
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition rotate_postcond_dec (a : list Z) (offset : Z) (result : list Z) : bool :=
  let len_eq := Nat.eqb (length result) (length a) in
  len_eq.
(* !benchmark @end postcond_aux *)

Definition rotate_postcond (a : (list Z)) (offset : Z) (result : (list Z)) (h_precond : rotate_precond a offset) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length a) /\
(forall i : nat, (i < length a)%nat ->
  match nth_error result i with
  | Some r_val =>
      let idx := ((Z.of_nat i) + offset)%Z in
      let len_z := Z.of_nat (length a) in
      let idx_mod := (idx mod len_z)%Z in
      let idx_nat := Z.to_nat idx_mod in
      match nth_error a idx_nat with
      | Some a_val => r_val = a_val
      | None => True
      end
  | None => True
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rotate_postcond_satisfied (a : (list Z)) (offset : Z) (h_precond : rotate_precond a offset) :
    rotate_postcond a offset (rotate a offset h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
