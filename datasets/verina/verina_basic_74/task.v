(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition maxArray_precond_dec (a : list Z) : bool :=
  match length a with
  | O => false
  | S _ => true
  end.
(* !benchmark @end precond_aux *)

Definition maxArray_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxArray_aux (a : list Z) (index : nat) (current : Z) (fuel : nat) : Z :=
  match fuel with
  | O => current
  | S fuel' =>
      if (index <? length a)%nat then
        match nth_error a index with
        | Some elem =>
            let new_current := if (current >? elem)%Z then current else elem in
            maxArray_aux a (index + 1)%nat new_current fuel'
        | None => current
        end
      else
        current
  end.
(* !benchmark @end code_aux *)

Definition maxArray (a : (list Z)) (h_precond : maxArray_precond a) : Z :=
  (* !benchmark @start code *)
  match a with
| [] => 0
| hd :: tl => maxArray_aux a 1%nat hd (length a)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition maxArray_postcond_dec (a : list Z) (result : Z) : bool :=
  let all_geq := forallb (fun elem => (result >=? elem)%Z) a in
  let exists_eq := existsb (fun elem => (result =? elem)%Z) a in
  andb all_geq exists_eq.
(* !benchmark @end postcond_aux *)

Definition maxArray_postcond (a : (list Z)) (result : Z) (h_precond : maxArray_precond a) : Prop :=
  (* !benchmark @start postcond *)
  (forall (k : nat), (k < length a)%nat -> 
  match nth_error a k with
  | Some elem => (result >= elem)%Z
  | None => True
  end) /\
(exists (k : nat), (k < length a)%nat /\
  match nth_error a k with
  | Some elem => result = elem
  | None => False
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxArray_postcond_satisfied (a : (list Z)) (h_precond : maxArray_precond a) :
    maxArray_postcond a (maxArray a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
