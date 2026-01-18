(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
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
(* precondition helpers including _dec version, complete definitions *)
Definition LongestIncreasingSubsequence_precond_dec (a : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition LongestIncreasingSubsequence_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition intMax (x y : Z) : Z :=
  if (x <? y)%Z then y else x.

Fixpoint update_dp (dp : list Z) (a : list Z) (i j : nat) : list Z :=
  match j with
  | 0%nat => 
      match nth_error a 0%nat, nth_error a i, nth_error dp 0%nat, nth_error dp i with
      | Some aj, Some ai, Some dpj, Some dpi =>
          if (aj <? ai)%Z then
            let newVal := intMax dpi (dpj + 1)%Z in
            match i with
            | 0%nat => [newVal]
            | S i' => (firstn i dp) ++ [newVal] ++ (skipn (S i) dp)
            end
          else dp
      | _, _, _, _ => dp
      end
  | S j' =>
      let dp' := update_dp dp a i j' in
      match nth_error a (S j'), nth_error a i, nth_error dp' (S j'), nth_error dp' i with
      | Some aj, Some ai, Some dpj, Some dpi =>
          if (aj <? ai)%Z then
            let newVal := intMax dpi (dpj + 1)%Z in
            match i with
            | 0%nat => [newVal]
            | S i' => (firstn i dp') ++ [newVal] ++ (skipn (S i) dp')
            end
          else dp'
      | _, _, _, _ => dp'
      end
  end.

Fixpoint outer_loop (dp : list Z) (a : list Z) (i n : nat) : list Z :=
  match n with
  | 0%nat => dp
  | S n' =>
      match i with
      | 0%nat => dp
      | S i' =>
          let dp' := outer_loop dp a i' n' in
          match i' with
          | 0%nat => update_dp dp' a 1%nat 0%nat
          | _ => update_dp dp' a i (pred i)
          end
      end
  end.

Fixpoint list_max (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | [x] => x
  | x :: xs => intMax x (list_max xs)
  end.
(* !benchmark @end code_aux *)

Definition LongestIncreasingSubsequence (a : (list Z)) (h_precond : LongestIncreasingSubsequence_precond a) : Z :=
  (* !benchmark @start code *)
  let n := length a in
  let dp := repeat 1%Z n in
  let dp_final := outer_loop dp a (pred n) (pred n) in
  match dp_final with
  | [] => 0%Z
  | _ => list_max dp_final
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint subsequences {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs =>
      let subs := subsequences xs in
      subs ++ map (fun sub => x :: sub) subs
  end.

Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: rest =>
      if (x <? y)%Z then is_strictly_increasing (y :: rest) else false
  end.

Definition LongestIncreasingSubsequence_postcond_dec (a : list Z) (result : Z) : bool :=
  let allSubseq := subsequences a in
  let increasingSubseqs := filter is_strictly_increasing allSubseq in
  let increasingSubseqLens := map (fun l => Z.of_nat (length l)) increasingSubseqs in
  existsb (Z.eqb result) increasingSubseqLens &&
  forallb (fun len => (len <=? result)%Z) increasingSubseqLens.
(* !benchmark @end postcond_aux *)

Definition LongestIncreasingSubsequence_postcond (a : (list Z)) (result : Z) (h_precond : LongestIncreasingSubsequence_precond a) : Prop :=
  (* !benchmark @start postcond *)
  let allSubseq := subsequences a in
  let increasingSubseqs := filter is_strictly_increasing allSubseq in
  let increasingSubseqLens := map (fun l => Z.of_nat (length l)) increasingSubseqs in
  In result increasingSubseqLens /\ Forall (fun len => (len <= result)%Z) increasingSubseqLens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestIncreasingSubsequence_postcond_satisfied (a : (list Z)) (h_precond : LongestIncreasingSubsequence_precond a) :
    LongestIncreasingSubsequence_postcond a (LongestIncreasingSubsequence a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
