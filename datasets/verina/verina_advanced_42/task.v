(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
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
Definition maxProfit_precond_dec (prices : list nat) : bool := true.
(* !benchmark @end precond_aux *)

Definition maxProfit_precond (prices : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition updateMinAndProfit (price : nat) (minSoFar : nat) (maxProfit : nat) : (nat * nat) :=
  let newMin := Nat.min minSoFar price in
  let profit := if Nat.ltb minSoFar price then price - minSoFar else 0%nat in
  let newMaxProfit := Nat.max maxProfit profit in
  (newMin, newMaxProfit).

Fixpoint maxProfitAux (prices : list nat) (minSoFar : nat) (maxProfit : nat) : nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let '(newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit in
    maxProfitAux ps newMin newProfit
  end.
(* !benchmark @end code_aux *)

Definition maxProfit (prices : (list nat)) (h_precond : maxProfit_precond prices) : nat :=
  (* !benchmark @start code *)
  match prices with
  | [] => 0%nat
  | p :: ps => maxProfitAux ps p 0%nat
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint zipIdx_aux {A : Type} (l : list A) (idx : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: zipIdx_aux xs (S idx)
  end.

Definition zipIdx {A : Type} (l : list A) : list (A * nat) :=
  zipIdx_aux l 0%nat.

Fixpoint list_all {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => f x && list_all f xs
  end.

Fixpoint list_any {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => f x || list_any f xs
  end.

Definition maxProfit_postcond_dec (prices : list nat) (result : nat) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition maxProfit_postcond (prices : (list nat)) (result : nat) (h_precond : maxProfit_precond prices) : Prop :=
  (* !benchmark @start postcond *)
  let indexed := zipIdx prices in
  (* All valid transactions have profit ≤ result *)
  (forall pi i pj j, In (pi, i) indexed -> In (pj, j) indexed -> (i < j)%nat -> (pj - pi <= result)%nat) /\
  (* result = 0 when no profitable transaction exists *)
  ((result = 0%nat) <->
    ((length prices <= 1)%nat \/
     (forall pi i, In (pi, i) indexed ->
       forall pj j, In (pj, j) indexed -> (i >= j)%nat \/ (pj <= pi)%nat))) /\
  (* If result > 0, there exists a transaction achieving it *)
  ((result > 0)%nat -> exists pi i pj j, In (pi, i) indexed /\ In (pj, j) indexed /\ (i < j)%nat /\ pj - pi = result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxProfit_postcond_satisfied (prices : (list nat)) (h_precond : maxProfit_precond prices) :
    maxProfit_postcond prices (maxProfit prices h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
