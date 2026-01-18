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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition twoSum_precond_dec (nums : list Z) (target : Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint inner (x : Z) (target : Z) (lst' : list Z) (j : nat) : option nat :=
  match lst' with
  | [] => None
  | y :: ys =>
      if (x + y =? target)%Z then
        Some j
      else
        inner x target ys (j + 1%nat)
  end.

Fixpoint outer (nums : list Z) (target : Z) (lst : list Z) (i : nat) : option (nat * nat) :=
  match lst with
  | [] => None
  | x :: xs =>
      match inner x target xs (i + 1%nat) with
      | Some j => Some (i, j)
      | None => outer nums target xs (i + 1%nat)
      end
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) : (option (nat  * nat)) :=
  (* !benchmark @start code *)
  outer nums target nums 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if all elements in a list satisfy a property *)
Fixpoint all {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => p x && all p xs
  end.

(* Helper to zip a list with indices *)
Fixpoint zipIdx {A : Type} (l : list A) (idx : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: zipIdx xs (idx + 1%nat)
  end.

Definition zipIdx0 {A : Type} (l : list A) : list (A * nat) := zipIdx l 0%nat.

(* Pairwise predicate *)
Inductive Pairwise {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
  | Pairwise_nil : Pairwise R []
  | Pairwise_cons : forall x xs,
      Forall (R x) xs ->
      Pairwise R xs ->
      Pairwise R (x :: xs).

Definition twoSum_postcond_dec (nums : list Z) (target : Z) (result : option (nat * nat)) : bool :=
  match result with
  | None => true  (* We would need decidable Pairwise check - simplified *)
  | Some (i, j) =>
      (i <? j)%nat &&
      (j <? length nums)%nat &&
      (nth i nums 0 + nth j nums 0 =? target)%Z &&
      all (fun '(a, i') =>
        all (fun b => negb (a + b =? target)%Z)
            (skipn (i' + 1%nat) nums))
          (zipIdx0 (firstn i nums)) &&
      all (fun b => negb (nth i nums 0 + b =? target)%Z)
          (firstn (j - i - 1%nat)%nat (skipn (i + 1%nat) nums))
  end.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (option (nat  * nat))) (h_precond : twoSum_precond nums target) : Prop :=
  (* !benchmark @start postcond *)
  match result with
| None => Pairwise (fun a b => (a + b <> target)%Z) nums
| Some (i, j) =>
    (i < j)%nat /\
    (j < length nums)%nat /\
    (nth i nums 0 + nth j nums 0 = target)%Z /\
    (forall i' a,
      In (a, i') (zipIdx0 (firstn i nums)) ->
      forall b, In b (skipn (i' + 1%nat) nums) -> (a + b <> target)%Z) /\
    (forall b, In b (firstn (j - i - 1%nat)%nat (skipn (i + 1%nat) nums)) ->
      (nth i nums 0 + b <> target)%Z)
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
