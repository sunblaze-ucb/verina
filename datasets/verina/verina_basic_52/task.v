(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition BubbleSort_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default (d : Z) (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => d
  | x :: _, O => x
  | _ :: xs, S n' => nth_default d xs n'
  end.

Fixpoint set_nth (l : list Z) (n : nat) (v : Z) : list Z :=
  match l, n with
  | [], _ => []
  | _ :: xs, O => v :: xs
  | x :: xs, S n' => x :: set_nth xs n' v
  end.

Definition swap (a : list Z) (i j : nat) : list Z :=
  let vi := nth_default 0 a i in
  let vj := nth_default 0 a j in
  set_nth (set_nth a i vj) j vi.

Fixpoint bubbleInner (fuel : nat) (j i : nat) (a : list Z) : list Z :=
  match fuel with
  | O => a
  | S fuel' =>
    if (j <? i)%nat then
      let vj := nth_default 0 a j in
      let vj1 := nth_default 0 a (j + 1)%nat in
      let a' := if (vj >? vj1)%Z then swap a j (j + 1)%nat else a in
      bubbleInner fuel' (j + 1)%nat i a'
    else
      a
  end.

Fixpoint bubbleOuter (fuel : nat) (i : nat) (a : list Z) : list Z :=
  match fuel with
  | O => a
  | S fuel' =>
    match i with
    | O => a
    | S i' =>
      let a' := bubbleInner (length a) O i a in
      bubbleOuter fuel' i' a'
    end
  end.

Definition bubbleSort_impl (a : list Z) : list Z :=
  match length a with
  | O => a
  | S n => bubbleOuter (length a) n a
  end.
(* !benchmark @end code_aux *)

Definition BubbleSort (a : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  bubbleSort_impl a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <=? y)%Z && is_sorted xs
    end
  end.

Fixpoint count_occ_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_occ_Z x t) else count_occ_Z x t
  end.

Fixpoint is_perm_aux (l1 l2 : list Z) (check : list Z) : bool :=
  match check with
  | [] => true
  | x :: xs => ((count_occ_Z x l1 =? count_occ_Z x l2)%nat) && is_perm_aux l1 l2 xs
  end.

Definition is_perm (l1 l2 : list Z) : bool :=
  (length l1 =? length l2)%nat && is_perm_aux l1 l2 l1 && is_perm_aux l1 l2 l2.
(* !benchmark @end postcond_aux *)

Definition BubbleSort_postcond (a : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  is_sorted result && is_perm result a
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem BubbleSort_postcond_satisfied (a : (list Z)) :
    BubbleSort_precond a = true ->
    BubbleSort_postcond a (BubbleSort a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
