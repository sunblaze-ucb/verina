(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition LongestCommonSubsequence_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition intMax (x y : Z) : Z :=
  if x <? y then y else x.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n'
  end.

Fixpoint update_list {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  match l, idx with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S n' => h :: update_list t n' v
  end.

Definition get_dp (dp : list (list Z)) (i j : nat) : Z :=
  nth_Z (nth i dp []) j.

Definition set_dp (dp : list (list Z)) (i j : nat) (v : Z) : list (list Z) :=
  let row := nth i dp [] in
  let new_row := update_list row j v in
  update_list dp i new_row.

Fixpoint inner_loop (a b : list Z) (dp : list (list Z)) (i j : nat) (n : nat) : list (list Z) :=
  match n with
  | O => dp
  | S n' =>
    if (j =? 0)%nat then
      inner_loop a b dp i (j + 1)%nat n'
    else if (i =? 0)%nat then
      inner_loop a b dp i (j + 1)%nat n'
    else
      let ai := nth_Z a (i - 1)%nat in
      let bj := nth_Z b (j - 1)%nat in
      let new_dp :=
        if ai =? bj then
          let newVal := (get_dp dp (i - 1)%nat (j - 1)%nat) + 1 in
          set_dp dp i j newVal
        else
          let newVal := intMax (get_dp dp (i - 1)%nat j) (get_dp dp i (j - 1)%nat) in
          set_dp dp i j newVal
      in
      inner_loop a b new_dp i (j + 1)%nat n'
  end.

Fixpoint outer_loop (a b : list Z) (dp : list (list Z)) (i : nat) (m n : nat) : list (list Z) :=
  match m with
  | O => dp
  | S m' =>
    let dp' := inner_loop a b dp i 0%nat (n + 1)%nat in
    outer_loop a b dp' (i + 1)%nat m' n
  end.

Definition make_dp (m n : nat) : list (list Z) :=
  let row := repeat 0 (n + 1)%nat in
  repeat row (m + 1)%nat.
(* !benchmark @end code_aux *)

Definition LongestCommonSubsequence (a : (list Z)) (b : (list Z)) : Z :=
  (* !benchmark @start code *)
  let m := length a in
  let n := length b in
  let dp := make_dp m n in
  let dp' := outer_loop a b dp 0%nat (m + 1)%nat n in
  get_dp dp' m n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_subseq_aux (l : list Z) : list (list Z) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    let subs := all_subseq_aux xs in
    subs ++ map (fun sub => x :: sub) subs
  end.

Definition all_subseq (l : list Z) : list (list Z) :=
  all_subseq_aux l.

Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2) && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition list_contains (ls : list (list Z)) (l : list Z) : bool :=
  existsb (fun x => list_Z_eqb x l) ls.

Definition common_subseq_lens (a b : list Z) : list nat :=
  let subseqA := all_subseq a in
  let subseqB := all_subseq b in
  let common := filter (fun l => list_contains subseqB l) subseqA in
  map (fun l => length l) common.

Definition nat_list_contains (l : list nat) (n : nat) : bool :=
  existsb (fun x => (x =? n)%nat) l.
(* !benchmark @end postcond_aux *)

Definition LongestCommonSubsequence_postcond (a : (list Z)) (b : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let lens := common_subseq_lens a b in
  let result_nat := Z.to_nat result in
  nat_list_contains lens result_nat && forallb (fun x => (x <=? result_nat)%nat) lens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestCommonSubsequence_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    LongestCommonSubsequence_precond a b = true ->
    LongestCommonSubsequence_postcond a b (LongestCommonSubsequence a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
