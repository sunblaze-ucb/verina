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

(* !benchmark @end precond_aux *)

Definition containsConsecutiveNumbers_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n'
  end.

Fixpoint checkConsecutive (l : list Z) (i : nat) (len : nat) : bool :=
  match len with
  | O => false
  | S O => false
  | S (S _ as len') =>
    match i with
    | O => 
      let x := nth_Z l 0 in
      let y := nth_Z l 1 in
      if (x + 1 =? y)%Z then true
      else checkConsecutive l 1 len'
    | S i' =>
      if (i <? len')%nat then
        let x := nth_Z l i in
        let y := nth_Z l (S i) in
        if (x + 1 =? y)%Z then true
        else checkConsecutive l (S i) (len' - i')%nat
      else false
    end
  end.

Fixpoint hasConsecutivePair (l : list Z) : bool :=
  match l with
  | [] => false
  | [_] => false
  | x :: ((y :: _) as rest) =>
    if (x + 1 =? y)%Z then true
    else hasConsecutivePair rest
  end.
(* !benchmark @end code_aux *)

Definition containsConsecutiveNumbers (a : (list Z)) : bool :=
  (* !benchmark @start code *)
  hasConsecutivePair a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint existsConsecutiveAt (l : list Z) (i : nat) : bool :=
  match l with
  | [] => false
  | [_] => false
  | x :: ((y :: _) as rest) =>
    if (x + 1 =? y)%Z then true
    else existsConsecutiveAt rest (S i)
  end.

Fixpoint nth_Z_post (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z_post t n'
  end.

Fixpoint checkExistsConsec (l : list Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    let i := (length l - S fuel')%nat in
    if (S i <? length l)%nat then
      if (nth_Z_post l i + 1 =? nth_Z_post l (S i))%Z then true
      else checkExistsConsec l fuel'
    else checkExistsConsec l fuel'
  end.

Definition existsConsecutive (l : list Z) : bool :=
  checkExistsConsec l (length l).
(* !benchmark @end postcond_aux *)

Definition containsConsecutiveNumbers_postcond (a : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (existsConsecutive a) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem containsConsecutiveNumbers_postcond_satisfied (a : (list Z)) :
    containsConsecutiveNumbers_precond a = true ->
    containsConsecutiveNumbers_postcond a (containsConsecutiveNumbers a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
