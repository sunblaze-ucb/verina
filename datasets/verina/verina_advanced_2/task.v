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
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to compute maximum of two integers *)
Definition intMax (x y : Z) : Z :=
  if (x <? y)%Z then y else x.

(* Helper to get element at index with default *)
Fixpoint nth_default {A : Type} (l : list A) (n : nat) (default : A) : A :=
  match n, l with
  | O, x :: _ => x
  | S m, _ :: t => nth_default t m default
  | _, [] => default
  end.

(* Helper to set element at index *)
Fixpoint set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match n, l with
  | O, _ :: t => v :: t
  | S m, h :: t => h :: set_nth t m v
  | _, [] => []
  end.

(* Initialize a list with given length and value *)
Fixpoint repeat_list {A : Type} (n : nat) (v : A) : list A :=
  match n with
  | O => []
  | S m => v :: repeat_list m v
  end.

(* Nested loop computation for DP table *)
Fixpoint compute_dp_inner (a b : list Z) (dp : list (list Z)) (i j : nat) (n : nat) : list (list Z) :=
  match n with
  | O => dp
  | S n' =>
      let dp' :=
        if (Nat.eqb i 0%nat) || (Nat.eqb j 0%nat) then dp
        else if (nth_default a (i - 1) 0 =? nth_default b (j - 1) 0)%Z then
          let oldRow := nth_default dp i [] in
          let newVal := (nth_default (nth_default dp (i - 1) []) (j - 1) 0 + 1)%Z in
          let newRow := set_nth oldRow j newVal in
          set_nth dp i newRow
        else
          let oldRow := nth_default dp i [] in
          let newVal := intMax (nth_default (nth_default dp (i - 1) []) j 0)
                                (nth_default oldRow (j - 1) 0) in
          let newRow := set_nth oldRow j newVal in
          set_nth dp i newRow
      in
      compute_dp_inner a b dp' i (j + 1) n'
  end.

Fixpoint compute_dp_outer (a b : list Z) (dp : list (list Z)) (i m n : nat) (fuel : nat) : list (list Z) :=
  match fuel with
  | O => dp
  | S fuel' =>
      let dp' := compute_dp_inner a b dp i 0%nat (n + 1) in
      compute_dp_outer a b dp' (i + 1) m n fuel'
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition LongestCommonSubsequence_precond_dec (a : list Z) (b : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition LongestCommonSubsequence_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* All subsequences of a list *)
Fixpoint allSubseq_aux {A : Type} (l : list A) (fuel : nat) : list (list A) :=
  match fuel with
  | O => [[]]
  | S fuel' =>
      match l with
      | [] => [[]]
      | x :: xs =>
          let rest := allSubseq_aux xs fuel' in
          rest ++ (map (fun sub => x :: sub) rest)
      end
  end.

Definition allSubseq {A : Type} (l : list A) : list (list A) :=
  allSubseq_aux l (length l).
(* !benchmark @end code_aux *)

Definition LongestCommonSubsequence (a : (list Z)) (b : (list Z)) (h_precond : LongestCommonSubsequence_precond a b) : Z :=
  (* !benchmark @start code *)
  let m := length a in
  let n := length b in
  let init_row := repeat_list (n + 1) 0%Z in
  let init_dp := repeat_list (m + 1) init_row in
  let dp := compute_dp_outer a b init_dp 0%nat m n (m + 1) in
  nth_default (nth_default dp m []) n 0%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if list contains element (for Z lists) *)
Fixpoint contains_Z (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else contains_Z t x
  end.

(* Helper to check if two lists are equal *)
Fixpoint list_eqb {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => if eq_dec x y then list_eqb eq_dec xs ys else false
  | _, _ => false
  end.

(* Helper to check if list contains sublist (generic) *)
Fixpoint contains_list {A : Type} (eq_dec : A -> A -> bool) (ll : list (list A)) (l : list A) : bool :=
  match ll with
  | [] => false
  | h :: t => if list_eqb eq_dec h l then true else contains_list eq_dec t l
  end.

(* Helper to check if all elements in list satisfy predicate *)
Fixpoint all_Z (f : Z -> bool) (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => if f h then all_Z f t else false
  end.

Definition LongestCommonSubsequence_postcond_dec (a b : list Z) (result : Z) : bool :=
  let subseqA := allSubseq a in
  let subseqB := allSubseq b in
  let commonSubseq := filter (fun l => contains_list Z.eqb subseqB l) subseqA in
  let commonSubseqLens := map (fun l => Z.of_nat (length l)) commonSubseq in
  (contains_Z commonSubseqLens result) && (all_Z (fun x => (x <=? result)%Z) commonSubseqLens).
(* !benchmark @end postcond_aux *)

Definition LongestCommonSubsequence_postcond (a : (list Z)) (b : (list Z)) (result : Z) (h_precond : LongestCommonSubsequence_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  let subseqA := allSubseq a in
  let subseqB := allSubseq b in
  let commonSubseq := filter (fun l => contains_list Z.eqb subseqB l) subseqA in
  let commonSubseqLens := map (fun l => Z.of_nat (length l)) commonSubseq in
  In result commonSubseqLens /\ Forall (fun x => (x <= result)%Z) commonSubseqLens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestCommonSubsequence_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : LongestCommonSubsequence_precond a b) :
    LongestCommonSubsequence_postcond a b (LongestCommonSubsequence a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
