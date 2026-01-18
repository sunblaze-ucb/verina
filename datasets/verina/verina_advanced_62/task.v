(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
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
Fixpoint all_non_negative (l : list Z) : Prop :=
  match l with
  | [] => True
  | h :: t => (h >= 0) /\ all_non_negative t
  end.

Fixpoint all_non_negative_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => (h >=? 0) && all_non_negative_dec t
  end.

Definition rain_precond_dec (heights : list Z) : bool :=
  all_non_negative_dec heights.
(* !benchmark @end precond_aux *)

Definition rain_precond (heights : (list (Z))) : Prop :=
  (* !benchmark @start precond *)
  all_non_negative heights
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Fixpoint nth_default (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | h :: _, O => h
  | _ :: t, S n' => nth_default t n' default
  end.

Fixpoint rain_aux (heights : list Z) (left right : nat) (leftMax rightMax water : Z) (fuel : nat) : Z :=
  match fuel with
  | O => water
  | S fuel' =>
      if (left >=? right)%nat then
        water
      else
        let h_left := nth_default heights left 0 in
        let h_right := nth_default heights right 0 in
        if (h_left <=? h_right) then
          let newLeftMax := Z.max leftMax h_left in
          let newWater := (water + Z.max 0 (leftMax - h_left))%Z in
          rain_aux heights (left + 1)%nat right newLeftMax rightMax newWater fuel'
        else
          let newRightMax := Z.max rightMax h_right in
          let newWater := (water + Z.max 0 (rightMax - h_right))%Z in
          rain_aux heights left (right - 1)%nat leftMax newRightMax newWater fuel'
  end.
(* !benchmark @end code_aux *)

Definition rain (heights : (list (Z))) (h_precond : rain_precond heights) : Z :=
  (* !benchmark @start code *)
  let n := length heights in
if (n <? 3)%nat then 0
else
  let h0 := nth_default heights 0%nat 0 in
  let hn := nth_default heights (n - 1)%nat 0 in
  rain_aux heights 0%nat (n - 1)%nat h0 hn 0 n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Fixpoint max_left_at (heights : list Z) (i j : nat) (max_so_far : Z) (fuel : nat) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
      if (j >? i)%nat then max_so_far
      else
        let h := nth_default heights j 0 in
        max_left_at heights i (j + 1)%nat (Z.max max_so_far h) fuel'
  end.

Fixpoint max_right_at (heights : list Z) (i : nat) (j : nat) (max_so_far : Z) (fuel : nat) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
      if (j >=? length heights)%nat then max_so_far
      else
        let h := nth_default heights j 0 in
        max_right_at heights i (j + 1)%nat (Z.max max_so_far h) fuel'
  end.

Definition water_at (heights : list Z) (i : nat) : Z :=
  let ml := max_left_at heights i 0%nat 0 (i + 2)%nat in
  let mr := max_right_at heights i i 0 (length heights - i + 1)%nat in
  let h := nth_default heights i 0 in
  Z.max 0 (Z.min ml mr - h).

Fixpoint sum_water (heights : list Z) (i : nat) (acc : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if (i >=? length heights)%nat then acc
      else sum_water heights (i + 1)%nat (acc + water_at heights i) fuel'
  end.

Definition rain_postcond_dec (heights : list Z) (result : Z) : bool :=
  let n := length heights in
  (result >=? 0) &&
  (if (n <? 3)%nat then (result =? 0)
   else (result =? sum_water heights 0%nat 0 (n + 1)%nat)).
(* !benchmark @end postcond_aux *)

Definition rain_postcond (heights : (list (Z))) (result : Z) (h_precond : rain_precond heights) : Prop :=
  (* !benchmark @start postcond *)
  (result >= 0) /\
(if (length heights <? 3)%nat then result = 0
 else result = sum_water heights 0%nat 0 (length heights + 1)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rain_postcond_satisfied (heights : (list (Z))) (h_precond : rain_precond heights) :
    rain_postcond heights (rain heights h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
