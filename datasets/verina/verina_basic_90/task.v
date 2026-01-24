(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition get2d (a : list (list Z)) (i j : Z) : Z :=
  let row := nth (Z.to_nat i) a [] in
  nth (Z.to_nat j) row 0.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_Z_pairwise_le (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && list_Z_pairwise_le tl
  end.

Fixpoint list_nat_pairwise_eq (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x =? y)%nat && list_nat_pairwise_eq tl
  end.

Definition get_column (a : list (list Z)) (i : nat) : list Z :=
  map (fun row => nth i row 0) a.
(* !benchmark @end precond_aux *)

Definition SlopeSearch_precond (a : (list (list Z))) (key : Z) : bool :=
  (* !benchmark @start precond *)
  match a with
    | [] => false
    | row0 :: _ =>
      let rows := length a in
      let cols := length row0 in
      (1 <=? rows)%nat &&
      (1 <=? cols)%nat &&
      list_nat_pairwise_eq (map (fun r => length r) a) &&
      forallb (fun row => list_Z_pairwise_le row) a &&
      forallb (fun i => list_Z_pairwise_le (get_column a i)) (seq 0 cols)
    end
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint slope_search_aux (a : list (list Z)) (key : Z) (rows cols : nat) (m n : Z) (fuel : nat) : (Z * Z) :=
  match fuel with
  | O => (-1, -1)
  | S fuel' =>
    if orb (m >=? Z.of_nat rows) (n <? 0) then (-1, -1)
    else
      let v := get2d a m n in
      if v =? key then (m, n)
      else if v <? key then slope_search_aux a key rows cols (m + 1) n fuel'
      else slope_search_aux a key rows cols m (n - 1) fuel'
  end.
(* !benchmark @end code_aux *)

Definition SlopeSearch (a : (list (list Z))) (key : Z) : (Z  * Z) :=
  (* !benchmark @start code *)
  let rows := length a in
    let cols := match a with [] => O | row0 :: _ => length row0 end in
    slope_search_aux a key rows cols 0 (Z.of_nat (cols - 1)) (rows + cols)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition all_elements_neq (a : list (list Z)) (key : Z) : bool :=
  forallb (fun row => forallb (fun e => negb (e =? key)) row) a.
(* !benchmark @end postcond_aux *)

Definition SlopeSearch_postcond (a : (list (list Z))) (key : Z) (result : (Z  * Z)) : bool :=
  (* !benchmark @start postcond *)
  let '(m, n) := result in
    match a with
    | [] => false
    | row0 :: _ =>
      let rows := Z.of_nat (length a) in
      let cols := Z.of_nat (length row0) in
      ((m >=? 0) && (m <? rows) && (n >=? 0) && (n <? cols) && (get2d a m n =? key)) ||
      ((m =? -1) && (n =? -1) && all_elements_neq a key)
    end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SlopeSearch_postcond_satisfied (a : (list (list Z))) (key : Z) :
    SlopeSearch_precond a key = true ->
    SlopeSearch_postcond a key (SlopeSearch a key) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
