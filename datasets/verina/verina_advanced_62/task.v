(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  nth n l default.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition rain_precond (heights : (list (Z))) : bool :=
  (* !benchmark @start precond *)
  forallb (fun h => h >=? 0) heights
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint rain_aux (heights : list Z) (left right : nat) (leftMax rightMax water : Z) (fuel : nat) : Z :=
  match fuel with
  | O => water
  | S fuel' =>
    if (right <=? left)%nat then water
    else
      let hl := nth_Z heights left 0 in
      let hr := nth_Z heights right 0 in
      if hl <=? hr then
        let newLeftMax := Z.max leftMax hl in
        let newWater := water + Z.max 0 (leftMax - hl) in
        rain_aux heights (S left) right newLeftMax rightMax newWater fuel'
      else
        let newRightMax := Z.max rightMax hr in
        let newWater := water + Z.max 0 (rightMax - hr) in
        rain_aux heights left (right - 1)%nat leftMax newRightMax newWater fuel'
  end.
(* !benchmark @end code_aux *)

Definition rain (heights : (list (Z))) : Z :=
  (* !benchmark @start code *)
  let n := length heights in
  if (n <? 3)%nat then 0
  else
    let last_idx := (n - 1)%nat in
    let h0 := nth_Z heights 0 0 in
    let hn := nth_Z heights last_idx 0 in
    rain_aux heights 0 last_idx h0 hn 0 n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint max_left_at_aux (heights : list Z) (j i : nat) (max_so_far : Z) (fuel : nat) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
    if (i <? j)%nat then max_so_far
    else max_left_at_aux heights (S j) i (Z.max max_so_far (nth_Z heights j 0)) fuel'
  end.

Definition max_left_at (heights : list Z) (i : nat) : Z :=
  max_left_at_aux heights 0 i 0 (S i).

Fixpoint max_right_at_aux (heights : list Z) (j : nat) (max_so_far : Z) (fuel : nat) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
    if (length heights <=? j)%nat then max_so_far
    else max_right_at_aux heights (S j) (Z.max max_so_far (nth_Z heights j 0)) fuel'
  end.

Definition max_right_at (heights : list Z) (i : nat) : Z :=
  max_right_at_aux heights i 0 (S (length heights - i)).

Definition water_at (heights : list Z) (i : nat) : Z :=
  Z.max 0 (Z.min (max_left_at heights i) (max_right_at heights i) - nth_Z heights i 0).

Fixpoint sum_water_aux (heights : list Z) (i : nat) (acc : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
    if (length heights <=? i)%nat then acc
    else sum_water_aux heights (S i) (acc + water_at heights i) fuel'
  end.

Definition sum_water (heights : list Z) : Z :=
  sum_water_aux heights 0 0 (S (length heights)).
(* !benchmark @end postcond_aux *)

Definition rain_postcond (heights : (list (Z))) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  (result >=? 0) &&
  (if (length heights <? 3)%nat then (result =? 0)
   else (result =? sum_water heights))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem rain_postcond_satisfied (heights : (list (Z))) :
    rain_precond heights = true ->
    rain_postcond heights (rain heights) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
