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

Definition LongestIncreasingSubsequence_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition intMax (x y : Z) : Z :=
  if x <? y then y else x.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0
  | h :: t => match n with
              | O => h
              | S n' => nth_Z t n'
              end
  end.

Fixpoint update_list (l : list Z) (n : nat) (v : Z) : list Z :=
  match l with
  | [] => []
  | h :: t => match n with
              | O => v :: t
              | S n' => h :: update_list t n' v
              end
  end.

Fixpoint inner_loop (a : list Z) (dp : list Z) (i j : nat) : list Z :=
  match j with
  | O => dp
  | S j' =>
    let idx := (i - j)%nat in
    let dp' := if (nth_Z a idx <? nth_Z a i)
               then update_list dp i (intMax (nth_Z dp i) (nth_Z dp idx + 1))
               else dp
    in inner_loop a dp' i j'
  end.

Fixpoint outer_loop (a : list Z) (dp : list Z) (remaining : nat) (current : nat) : list Z :=
  match remaining with
  | O => dp
  | S r' =>
    let dp' := inner_loop a dp current current in
    outer_loop a dp' r' (S current)
  end.

Fixpoint make_ones (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => 1 :: make_ones n'
  end.

Fixpoint fold_max (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | h :: t => fold_max t (intMax acc h)
  end.
(* !benchmark @end code_aux *)

Definition LongestIncreasingSubsequence (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  let n := length a in
  match n with
  | O => 0
  | _ =>
    let dp := make_ones n in
    let dp' := outer_loop a dp (n - 1)%nat 1%nat in
    fold_max dp' 0
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint subsequences_aux (a : list Z) : list (list Z) :=
  match a with
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences_aux xs in
    subs ++ map (fun sub => x :: sub) subs
  end.

Definition subsequences (a : list Z) : list (list Z) :=
  subsequences_aux a.

Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: _ => (x <? y)%Z && is_strictly_increasing xs
    end
  end.

Definition increasing_subsequences (a : list Z) : list (list Z) :=
  filter is_strictly_increasing (subsequences a).

Definition increasing_subseq_lens (a : list Z) : list Z :=
  map (fun l => Z.of_nat (length l)) (increasing_subsequences a).

Fixpoint list_Z_contains (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | h :: t => (h =? x) || list_Z_contains t x
  end.

Definition all_leq (l : list Z) (x : Z) : bool :=
  forallb (fun y => y <=? x) l.
(* !benchmark @end postcond_aux *)

Definition LongestIncreasingSubsequence_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let lens := increasing_subseq_lens a in
  list_Z_contains lens result && all_leq lens result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestIncreasingSubsequence_postcond_satisfied (a : (list Z)) :
    LongestIncreasingSubsequence_precond a = true ->
    LongestIncreasingSubsequence_postcond a (LongestIncreasingSubsequence a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
