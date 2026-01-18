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
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition LongestCommonSubsequence_precond_dec (a : list Z) (b : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition LongestCommonSubsequence_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition intMax (x y : Z) : Z :=
  if (x <? y)%Z then y else x.

Fixpoint power_set_aux {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    let ps := power_set_aux xs in
    ps ++ map (fun sub => x :: sub) ps
  end.

Definition all_subseq (arr : list Z) : list (list Z) :=
  map (@rev Z) (power_set_aux arr).

Fixpoint list_mem {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eq_dec x y then true else list_mem eq_dec x ys
  end.

Fixpoint list_eq_dec (l1 l2 : list Z) : {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality. apply Z.eq_dec.
Defined.

Definition list_contains (l : list (list Z)) (x : list Z) : bool :=
  list_mem list_eq_dec x l.

Fixpoint get_2d (dp : list (list Z)) (i j : nat) : Z :=
  match nth_error dp i with
  | Some row => match nth_error row j with
                | Some v => v
                | None => 0
                end
  | None => 0
  end.

Fixpoint set_in_row (row : list Z) (j : nat) (val : Z) : list Z :=
  match j, row with
  | 0%nat, _ :: tl => val :: tl
  | S j', hd :: tl => hd :: set_in_row tl j' val
  | _, _ => row
  end.

Fixpoint set_2d (dp : list (list Z)) (i j : nat) (val : Z) : list (list Z) :=
  match i, dp with
  | 0%nat, row :: rest => set_in_row row j val :: rest
  | S i', row :: rest => row :: set_2d rest i' j val
  | _, _ => dp
  end.

Fixpoint get_list (l : list Z) (i : nat) : Z :=
  match nth_error l i with
  | Some v => v
  | None => 0
  end.

Fixpoint repeat_list {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | 0%nat => []
  | S n' => x :: repeat_list x n'
  end.

Fixpoint lcs_loop_j (dp : list (list Z)) (a b : list Z) (i j m n : nat) : list (list Z) :=
  match j with
  | 0%nat => dp
  | S j' =>
    let dp' := lcs_loop_j dp a b i j' m n in
    let actual_j := (n - j)%nat in
    let actual_i := (m - i)%nat in
    if (Nat.eqb actual_i 0%nat) || (Nat.eqb actual_j 0%nat) then
      dp'
    else if (get_list a (actual_i - 1)%nat =? get_list b (actual_j - 1)%nat)%Z then
      let newVal := (get_2d dp' (actual_i - 1)%nat (actual_j - 1)%nat + 1)%Z in
      set_2d dp' actual_i actual_j newVal
    else
      let newVal := intMax (get_2d dp' (actual_i - 1)%nat actual_j) (get_2d dp' actual_i (actual_j - 1)%nat) in
      set_2d dp' actual_i actual_j newVal
  end.

Fixpoint lcs_loop_i (dp : list (list Z)) (a b : list Z) (i m n : nat) : list (list Z) :=
  match i with
  | 0%nat => dp
  | S i' =>
    let dp' := lcs_loop_i dp a b i' m n in
    lcs_loop_j dp' a b (m - (m - i))%nat (S n) m n
  end.
(* !benchmark @end code_aux *)

Definition LongestCommonSubsequence (a : (list Z)) (b : (list Z)) (h_precond : LongestCommonSubsequence_precond a b) : Z :=
  (* !benchmark @start code *)
  let m := length a in
  let n := length b in
  let init_row := repeat_list 0 (S n) in
  let init_dp := repeat_list init_row (S m) in
  let dp := lcs_loop_i init_dp a b (S m) m n in
  get_2d dp m n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition LongestCommonSubsequence_postcond_dec (a : list Z) (b : list Z) (result : Z) : bool :=
  let subseqA := all_subseq a in
  let subseqB := all_subseq b in
  let commonSubseq := filter (fun l => list_contains subseqB l) subseqA in
  let commonSubseqLens := map (@length Z) commonSubseq in
  let contains_result := list_mem Z.eq_dec result commonSubseqLens in
  let all_le := forallb (fun len => (Z.of_nat len <=? result)%Z) commonSubseqLens in
  contains_result && all_le.
(* !benchmark @end postcond_aux *)

Definition LongestCommonSubsequence_postcond (a : (list Z)) (b : (list Z)) (result : Z) (h_precond : LongestCommonSubsequence_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  let allSubseq := all_subseq in
  let subseqA := allSubseq a in
  let subseqB := allSubseq b in
  let commonSubseq := filter (fun l => list_contains subseqB l) subseqA in
  let commonSubseqLens := map (@length Z) commonSubseq in
  In result (map Z.of_nat commonSubseqLens) /\ Forall (fun len => (Z.of_nat len <= result)%Z) commonSubseqLens
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
