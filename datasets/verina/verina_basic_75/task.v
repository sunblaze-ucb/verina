(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition minArray_precond_dec (a : list Z) : bool :=
  match length a with
  | O => false
  | _ => true
  end.
(* !benchmark @end precond_aux *)

Definition minArray_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a : list Z) (i : nat) (currentMin : Z) (fuel : nat) : Z :=
  match fuel with
  | O => currentMin
  | S fuel' =>
      if (i <? length a)%nat then
        match nth_error a i with
        | Some ai =>
            let newMin := if (currentMin >? ai)%Z then ai else currentMin in
            loop a (i + 1)%nat newMin fuel'
        | None => currentMin
        end
      else
        currentMin
  end.
(* !benchmark @end code_aux *)

Definition minArray (a : (list Z)) (h_precond : minArray_precond a) : Z :=
  (* !benchmark @start code *)
  match a with
| [] => 0%Z
| a0 :: _ => loop a 1%nat a0 (length a)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition minArray_postcond_dec (a : list Z) (result : Z) : bool :=
  let all_geq := forallb (fun x => (result <=? x)%Z) a in
  let exists_eq := existsb (fun x => (result =? x)%Z) a in
  andb all_geq exists_eq.
(* !benchmark @end postcond_aux *)

Definition minArray_postcond (a : (list Z)) (result : Z) (h_precond : minArray_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (forall i : nat, (i < length a)%nat -> match nth_error a i with Some ai => (result <= ai)%Z | None => True end) /\ (exists i : nat, (i < length a)%nat /\ match nth_error a i with Some ai => result = ai | None => False end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minArray_postcond_satisfied (a : (list Z)) (h_precond : minArray_precond a) :
    minArray_postcond a (minArray a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
