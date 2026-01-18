(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
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
(* Helper to check if any pair (i, j) with j < i sums to target *)
Fixpoint existsPairSumTo (nums : list Z) (target : Z) (i : nat) : Prop :=
  match i with
  | 0%nat => False
  | S i' =>
    (exists j, (j < i')%nat /\ nth i' nums 0 + nth j nums 0 = target) \/
    existsPairSumTo nums target i'
  end.

Definition hasExactlyOnePairProp (nums : list Z) (target : Z) : Prop :=
  exists! p : (nat * nat)%type, 
    let '(i, j) := p in
    (j < i < length nums)%nat /\ 
    nth i nums 0 + nth j nums 0 = target.

(* Helper to check if any j < i satisfies the sum condition *)
Fixpoint check_j (nums : list Z) (target : Z) (i' j : nat) : bool :=
  match j with
  | 0%nat => false
  | S j' => 
    if (nth i' nums 0 + nth j' nums 0 =? target)%Z then true
    else check_j nums target i' j'
  end.

(* Decidable version *)
Fixpoint existsPairSumTo_dec (nums : list Z) (target : Z) (i : nat) : bool :=
  match i with
  | 0%nat => false
  | S i' =>
    if check_j nums target i' i' then true else existsPairSumTo_dec nums target i'
  end.

Definition twoSum_precond_dec (nums : list Z) (target : Z) : bool :=
  ((length nums) >=? 2%nat)%nat && existsPairSumTo_dec nums target (length nums).
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  (length nums >= 2%nat)%nat /\
existsPairSumTo nums target (length nums) /\
hasExactlyOnePairProp nums target
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to find indices *)
Fixpoint findIndices (nums : list Z) (target : Z) (i j fuel : nat) : list nat :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
    if (i >=? length nums)%nat then
      []
    else if (j >=? length nums)%nat then
      findIndices nums target (i + 1)%nat (i + 2)%nat fuel'
    else
      if (nth i nums 0 + nth j nums 0 =? target)%Z then
        [i; j]
      else
        findIndices nums target i (j + 1)%nat fuel'
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) : (list nat) :=
  (* !benchmark @start code *)
  findIndices nums target 0%nat 1%nat (length nums * length nums)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Decidable version of postcondition *)
Definition twoSum_postcond_dec (nums : list Z) (target : Z) (result : list nat) : bool :=
  match result with
  | [i; j] =>
    ((length result) =? 2)%nat &&
    (i <? length nums)%nat &&
    (j <? length nums)%nat &&
    (i <? j)%nat &&
    (nth i nums 0 + nth j nums 0 =? target)%Z
  | _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (list nat)) (h_precond : twoSum_precond nums target) : Prop :=
  (* !benchmark @start postcond *)
  (length result = 2)%nat /\
(exists i j, result = [i; j] /\
  (i < length nums)%nat /\
  (j < length nums)%nat /\
  (i < j)%nat /\
  nth i nums 0 + nth j nums 0 = target)
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
