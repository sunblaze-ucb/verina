(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
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
(* Helper to check if all inner lists have the same length *)
Definition all_same_length (a : list (list Z)) : Prop :=
  match a with
  | [] => True
  | hd :: tl => Forall (fun row => length row = length hd) tl
  end.

Definition all_same_length_dec (a : list (list Z)) : bool :=
  match a with
  | [] => true
  | hd :: tl => forallb (fun row => Nat.eqb (length row) (length hd)) tl
  end.

(* Helper to check if a list is sorted in non-decreasing order *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: tl) as rest => (x <= y) /\ is_sorted rest
  end.

Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: tl) as rest => (x <=? y) && is_sorted_dec rest
  end.

(* Helper to check if all rows are sorted *)
Definition all_rows_sorted (a : list (list Z)) : Prop :=
  Forall is_sorted a.

Definition all_rows_sorted_dec (a : list (list Z)) : bool :=
  forallb is_sorted_dec a.

(* Helper to get the i-th element of the j-th column across all rows *)
Fixpoint get_column (a : list (list Z)) (col : nat) : list Z :=
  match a with
  | [] => []
  | row :: rest => 
      match nth_error row col with
      | Some v => v :: get_column rest col
      | None => get_column rest col
      end
  end.

(* Helper to check if all columns are sorted *)
Fixpoint all_columns_sorted_aux (a : list (list Z)) (ncols : nat) (fuel : nat) : Prop :=
  match fuel with
  | O => True
  | S fuel' =>
      match ncols with
      | O => True
      | S ncols' => is_sorted (get_column a ncols') /\ all_columns_sorted_aux a ncols' fuel'
      end
  end.

Definition all_columns_sorted (a : list (list Z)) : Prop :=
  match a with
  | [] => True
  | hd :: _ => all_columns_sorted_aux a (length hd) (length hd)
  end.

Fixpoint all_columns_sorted_aux_dec (a : list (list Z)) (ncols : nat) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      match ncols with
      | O => true
      | S ncols' => is_sorted_dec (get_column a ncols') && all_columns_sorted_aux_dec a ncols' fuel'
      end
  end.

Definition all_columns_sorted_dec (a : list (list Z)) : bool :=
  match a with
  | [] => true
  | hd :: _ => all_columns_sorted_aux_dec a (length hd) (length hd)
  end.

Definition SlopeSearch_precond_dec (a : list (list Z)) (key : Z) : bool :=
  match a with
  | [] => false
  | hd :: _ =>
      Nat.ltb 0%nat (length a) &&
      Nat.ltb 0%nat (length hd) &&
      all_same_length_dec a &&
      all_rows_sorted_dec a &&
      all_columns_sorted_dec a
  end.
(* !benchmark @end precond_aux *)

Definition SlopeSearch_precond (a : (list (list Z))) (key : Z) : Prop :=
  (* !benchmark @start precond *)
  ((length a) > 0%nat)%nat /\
  match a with
  | [] => False
  | hd :: _ => ((length hd) > 0%nat)%nat
  end /\
  all_same_length a /\
  all_rows_sorted a /\
  all_columns_sorted a
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition get2d (a : list (list Z)) (i j : Z) : Z :=
  match nth_error a (Z.to_nat i) with
  | Some row => match nth_error row (Z.to_nat j) with
                | Some v => v
                | None => 0
                end
  | None => 0
  end.

Fixpoint SlopeSearch_aux (a : list (list Z)) (key : Z) (rows cols : Z) (m n : Z) (fuel : nat) : (Z * Z) :=
  match fuel with
  | O => (-1, -1)
  | S fuel' =>
      if (m >=? rows) || (n <? 0) then (-1, -1)
      else
        let current := get2d a m n in
        if current =? key then (m, n)
        else if current <? key then
          SlopeSearch_aux a key rows cols (m + 1) n fuel'
        else
          SlopeSearch_aux a key rows cols m (n - 1) fuel'
  end.
(* !benchmark @end code_aux *)

Definition SlopeSearch (a : (list (list Z))) (key : Z) (h_precond : SlopeSearch_precond a key) : (Z  * Z) :=
  (* !benchmark @start code *)
  let rows := Z.of_nat (length a) in
  let cols := match a with
              | [] => 0
              | hd :: _ => Z.of_nat (length hd)
              end in
  SlopeSearch_aux a key rows cols 0 (cols - 1) (Z.to_nat (rows + cols))
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if key exists in the 2D array *)
Definition key_not_in_array (a : list (list Z)) (key : Z) : Prop :=
  Forall (fun row => Forall (fun e => e <> key) row) a.

Definition key_not_in_array_dec (a : list (list Z)) (key : Z) : bool :=
  forallb (fun row => forallb (fun e => negb (e =? key)) row) a.

Definition SlopeSearch_postcond_dec (a : list (list Z)) (key : Z) (result : Z * Z) : bool :=
  let (m, n) := result in
  let rows := Z.of_nat (length a) in
  let cols := match a with
              | [] => 0
              | hd :: _ => Z.of_nat (length hd)
              end in
  ((m >=? 0) && (m <? rows) && (n >=? 0) && (n <? cols) && (get2d a m n =? key)) ||
  ((m =? -1) && (n =? -1) && key_not_in_array_dec a key).
(* !benchmark @end postcond_aux *)

Definition SlopeSearch_postcond (a : (list (list Z))) (key : Z) (result : (Z  * Z)) (h_precond : SlopeSearch_precond a key) : Prop :=
  (* !benchmark @start postcond *)
  let (m, n) := result in
  let rows := Z.of_nat (length a) in
  let cols := match a with
              | [] => 0
              | hd :: _ => Z.of_nat (length hd)
              end in
  ((m >= 0) /\ (m < rows) /\ (n >= 0) /\ (n < cols) /\ get2d a m n = key) \/
  ((m = -1) /\ (n = -1) /\ key_not_in_array a key)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SlopeSearch_postcond_satisfied (a : (list (list Z))) (key : Z) (h_precond : SlopeSearch_precond a key) :
    SlopeSearch_postcond a key (SlopeSearch a key h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
