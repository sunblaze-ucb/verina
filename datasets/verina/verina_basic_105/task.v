(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition arrayProduct_precond_dec (a : list Z) (b : list Z) : bool :=
  Nat.eqb (length a) (length b).
(* !benchmark @end precond_aux *)

Definition arrayProduct_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  length a = length b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a b : list Z) (len : nat) (i : nat) (c : list Z) : list Z :=
  match len with
  | O => c
  | S len' =>
    if (i <? len)%nat then
      let a_val := if (i <? length a)%nat then nth i a 0%Z else 0%Z in
      let b_val := if (i <? length b)%nat then nth i b 0%Z else 0%Z in
      let new_c := 
        (firstn i c) ++ [a_val * b_val] ++ (skipn (i + 1%nat) c) in
      loop a b len' (i + 1%nat)%nat new_c
    else c
  end.
(* !benchmark @end code_aux *)

Definition arrayProduct (a : (list Z)) (b : (list Z)) (h_precond : arrayProduct_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let len := length a in
  let c := repeat 0%Z len in
  loop a b len 0%nat c
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition arrayProduct_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  andb (Nat.eqb (length result) (length a))
       (forallb (fun i => Z.eqb (nth i a 0%Z * nth i b 0%Z)%Z (nth i result 0%Z))
                (seq 0 (length a))).
(* !benchmark @end postcond_aux *)

Definition arrayProduct_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : arrayProduct_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (length result = length a) /\ (forall i, (i < length a)%nat -> (nth i a 0%Z * nth i b 0%Z)%Z = nth i result 0%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arrayProduct_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : arrayProduct_precond a b) :
    arrayProduct_postcond a b (arrayProduct a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
