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
Fixpoint has_distinct_pair (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: rest => orb (existsb (fun y => negb (x =? y)) rest) (has_distinct_pair rest)
  end.
(* !benchmark @end precond_aux *)

Definition secondSmallest_precond (s : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (2 <=? length s)%nat && has_distinct_pair s
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition nth_default (l : list Z) (n : nat) (d : Z) : Z :=
  nth n l d.

Fixpoint secondSmallestAux (s : list Z) (i minIdx secondIdx : nat) (fuel : nat) : Z :=
  match fuel with
  | O => nth_default s secondIdx 0
  | S fuel' =>
    if (length s <=? i)%nat then
      nth_default s secondIdx 0
    else
      let x := nth_default s i 0 in
      let m := nth_default s minIdx 0 in
      let smin := nth_default s secondIdx 0 in
      if x <? m then
        secondSmallestAux s (i + 1)%nat i minIdx fuel'
      else if x <? smin then
        secondSmallestAux s (i + 1)%nat minIdx i fuel'
      else
        secondSmallestAux s (i + 1)%nat minIdx secondIdx fuel'
  end.
(* !benchmark @end code_aux *)

Definition secondSmallest (s : (list Z)) : Z :=
  (* !benchmark @start code *)
  let v0 := nth_default s 0 0 in
  let v1 := nth_default s 1 0 in
  let '(minIdx, secondIdx) := if v1 <? v0 then (1%nat, 0%nat) else (0%nat, 1%nat) in
  secondSmallestAux s 2%nat minIdx secondIdx (length s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition existsb_idx {A : Type} (f : nat -> A -> bool) (l : list A) : bool :=
  let fix aux (l : list A) (idx : nat) : bool :=
    match l with
    | [] => false
    | x :: xs => orb (f idx x) (aux xs (S idx))
    end
  in aux l O.

Definition forallb_idx {A : Type} (f : nat -> A -> bool) (l : list A) : bool :=
  let fix aux (l : list A) (idx : nat) : bool :=
    match l with
    | [] => true
    | x :: xs => andb (f idx x) (aux xs (S idx))
    end
  in aux l O.

Definition nth_Z (l : list Z) (n : nat) : Z := nth n l 0.
(* !benchmark @end postcond_aux *)

Definition secondSmallest_postcond (s : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  existsb_idx (fun i _ => (i <? length s)%nat && (nth_Z s i =? result)) s &&
  existsb_idx (fun j _ =>
    (j <? length s)%nat &&
    (nth_Z s j <? result) &&
    forallb_idx (fun k _ =>
      implb ((k <? length s)%nat && negb (nth_Z s k =? nth_Z s j))
            (result <=? nth_Z s k)
    ) s
  ) s
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem secondSmallest_postcond_satisfied (s : (list Z)) :
    secondSmallest_precond s = true ->
    secondSmallest_postcond s (secondSmallest s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
