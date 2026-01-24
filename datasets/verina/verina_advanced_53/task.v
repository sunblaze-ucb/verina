(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_Z_nodup (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (fun y => (x =? y)%Z) xs) && list_Z_nodup xs
  end.
(* !benchmark @end precond_aux *)

Definition minimumRightShifts_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  list_Z_nodup nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isSortedAux (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => if (x <=? y)%Z then isSortedAux xs else false
    end
  end.

Definition rightShiftOnce (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | last :: revInit => last :: rev revInit
  end.

Fixpoint checkShifts (fuel : nat) (shifts_count : nat) (n : nat) (current_list : list Z) : Z :=
  match fuel with
  | O => (-1)%Z
  | S fuel' =>
    if (n <=? shifts_count)%nat then (-1)%Z
    else if isSortedAux current_list then Z.of_nat shifts_count
    else checkShifts fuel' (S shifts_count) n (rightShiftOnce current_list)
  end.
(* !benchmark @end code_aux *)

Definition minimumRightShifts (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  let n := length nums in
  if (n <=? 1)%nat then 0%Z
  else if isSortedAux nums then 0%Z
  else checkShifts n 1%nat n (rightShiftOnce nums)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint isSortedSpec (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => if (x <=? y)%Z then isSortedSpec xs else false
    end
  end.

Fixpoint rotateRight_aux (k : nat) (l : list Z) : list Z :=
  match k with
  | O => l
  | S k' =>
    match rev l with
    | [] => []
    | last :: revInit => rotateRight_aux k' (last :: rev revInit)
    end
  end.

Definition rightShiftK (k : nat) (l : list Z) : list Z :=
  rotateRight_aux k l.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.
(* !benchmark @end postcond_aux *)

Definition minimumRightShifts_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let n := length nums in
  if (n <=? 1)%nat then (result =? 0)%Z
  else
    ((result >=? 0)%Z &&
     (result <? Z.of_nat n)%Z &&
     isSortedSpec (rightShiftK (Z.to_nat result) nums) &&
     forallb (fun j => negb (isSortedSpec (rightShiftK j nums))) (range (Z.to_nat result)))
    ||
    ((result =? (-1))%Z &&
     forallb (fun k => negb (isSortedSpec (rightShiftK k nums))) (range n))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minimumRightShifts_postcond_satisfied (nums : (list Z)) :
    minimumRightShifts_precond nums = true ->
    minimumRightShifts_postcond nums (minimumRightShifts nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
