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
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition onlineMax_precond_dec (a : list Z) (x : nat) : bool :=
  ((Nat.ltb 0 (length a)) && (Nat.ltb 0 x) && (Nat.ltb x (length a)))%bool.
(* !benchmark @end precond_aux *)

Definition onlineMax_precond (a : (list Z)) (x : nat) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat /\ (x > 0)%nat /\ (x < length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findBest (a : list Z) (x : nat) (i : nat) (best : Z) (fuel : nat) : Z :=
  match fuel with
  | O => best
  | S fuel' =>
    if (i <? x)%nat then
      match nth_error a i with
      | Some ai =>
        let newBest := if (ai >? best) then ai else best in
        findBest a x (i + 1)%nat newBest fuel'
      | None => best
      end
    else best
  end.

Fixpoint findP (a : list Z) (x : nat) (m : Z) (i : nat) (fuel : nat) : nat :=
  match fuel with
  | O => (length a - 1)%nat
  | S fuel' =>
    if (i <? length a)%nat then
      match nth_error a i with
      | Some ai =>
        if (ai >? m) then i else findP a x m (i + 1)%nat fuel'
      | None => (length a - 1)%nat
      end
    else (length a - 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition onlineMax (a : (list Z)) (x : nat) (h_precond : onlineMax_precond a x) : (Z  * nat) :=
  (* !benchmark @start code *)
  match nth_error a 0 with
| Some best =>
  let m := findBest a x 1%nat best x in
  let p := findP a x m x (length a) in
  (m, p)
| None => (0, 0%nat)
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition onlineMax_postcond_dec (a : list Z) (x : nat) (result : Z * nat) : bool :=
  let '(m, p) := result in
  ((Nat.leb x p) && (Nat.ltb p (length a)))%bool.
(* !benchmark @end postcond_aux *)

Definition onlineMax_postcond (a : (list Z)) (x : nat) (result : (Z  * nat)) (h_precond : onlineMax_precond a x) : Prop :=
  (* !benchmark @start postcond *)
  let '(m, p) := result in
  (x <= p)%nat /\ (p < length a)%nat /\
  (forall i, (i < x)%nat -> match nth_error a i with Some ai => (ai <= m)%Z | None => True end) /\
  (exists i, (i < x)%nat /\ match nth_error a i with Some ai => ai = m | None => False end) /\
  ((p < length a - 1)%nat -> forall i, (i < p)%nat -> match nth_error a i, nth_error a p with
    | Some ai, Some ap => (ai < ap)%Z
    | _, _ => True
    end) /\
  ((forall i, (x <= i)%nat -> (i < length a)%nat -> match nth_error a i with Some ai => (ai <= m)%Z | None => True end) -> p = (length a - 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem onlineMax_postcond_satisfied (a : (list Z)) (x : nat) (h_precond : onlineMax_precond a x) :
    onlineMax_postcond a x (onlineMax a x h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
