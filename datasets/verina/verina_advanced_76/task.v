(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Nat.
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
Fixpoint eraseDups_Z (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if existsb (fun y => x =? y) xs then eraseDups_Z xs else x :: eraseDups_Z xs
  end.
(* !benchmark @end precond_aux *)

Definition topKFrequent_precond (nums : (list Z)) (k : nat) : bool :=
  (* !benchmark @start precond *)
  (k <=? length (eraseDups_Z nums))%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint find_pair (l : list (Z * nat)) (n : Z) : option (Z * nat) :=
  match l with
  | [] => None
  | (key, cnt) :: rest => if key =? n then Some (key, cnt) else find_pair rest n
  end.

Fixpoint update_freq (l : list (Z * nat)) (n : Z) : list (Z * nat) :=
  match l with
  | [] => []
  | (key, cnt) :: rest => 
      if key =? n then (key, (cnt + 1)%nat) :: rest 
      else (key, cnt) :: update_freq rest n
  end.

Definition add_or_update (acc : list (Z * nat)) (n : Z) : list (Z * nat) :=
  match find_pair acc n with
  | Some _ => update_freq acc n
  | None => acc ++ [(n, 1%nat)]
  end.

Definition build_freq_list (nums : list Z) : list (Z * nat) :=
  fold_left add_or_update nums [].

Fixpoint insertSorted (pair : Z * nat) (xs : list (Z * nat)) : list (Z * nat) :=
  let (x, cx) := pair in
  match xs with
  | [] => [pair]
  | (y, cy) :: ys => 
      if (cy <? cx)%nat then pair :: (y, cy) :: ys
      else (y, cy) :: insertSorted pair ys
  end.

Definition sort_by_freq (freqList : list (Z * nat)) : list (Z * nat) :=
  fold_left (fun acc pair => insertSorted pair acc) freqList [].

Fixpoint take_n {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: take_n n' xs
            end
  end.
(* !benchmark @end code_aux *)

Definition topKFrequent (nums : (list Z)) (k : nat) : (list Z) :=
  (* !benchmark @start code *)
  let freqList := build_freq_list nums in
  let sorted := sort_by_freq freqList in
  map fst (take_n k sorted)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | y :: ys => if x =? y then S (count_Z x ys) else count_Z x ys
  end.

Fixpoint pairwise {A : Type} (R : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => forallb (R x) xs && pairwise R xs
  end.

Fixpoint zipIdx_aux {A : Type} (l : list A) (idx : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: zipIdx_aux xs (S idx)
  end.

Definition zipIdx {A : Type} (l : list A) : list (A * nat) := zipIdx_aux l O.

Definition mem_Z (x : Z) (l : list Z) : bool := existsb (fun y => x =? y) l.

Definition freq_order_check (nums : list Z) (xi yj : Z * nat) : bool :=
  let (x, i) := xi in
  let (y, j) := yj in
  implb (i <? j)%nat (count_Z y nums <=? count_Z x nums)%nat.
(* !benchmark @end postcond_aux *)

Definition topKFrequent_postcond (nums : (list Z)) (k : nat) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? k)%nat) &&
  (forallb (fun x => mem_Z x nums) result) &&
  (pairwise (fun x y => negb (x =? y)) result) &&
  (forallb (fun x => 
    forallb (fun y => 
      mem_Z y result || (count_Z y nums <=? count_Z x nums)%nat
    ) nums
  ) result) &&
  (pairwise (freq_order_check nums) (zipIdx result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem topKFrequent_postcond_satisfied (nums : (list Z)) (k : nat) :
    topKFrequent_precond nums k = true ->
    topKFrequent_postcond nums k (topKFrequent nums k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
