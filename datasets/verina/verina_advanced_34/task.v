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
Require Import Coq.Arith.Arith.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to compute all subsequences *)
Fixpoint allSubseq_helper (nums : list Z) (acc : list (list Z)) : list (list Z) :=
  match nums with
  | [] => acc
  | x :: xs => 
      let new_acc := acc ++ map (fun sub => x :: sub) acc in
      allSubseq_helper xs new_acc
  end.

Definition allSubseq (nums : list Z) : list (list Z) :=
  map (@rev Z) (allSubseq_helper nums [[]]).

(* Check if a list is strictly increasing *)
Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl => 
      if (x <? y)%Z then is_strictly_increasing tl else false
  end.

(* Filter increasing subsequences and get their lengths *)
Definition increasingSubseqLens (nums : list Z) : list nat :=
  let all := allSubseq nums in
  let increasing := filter is_strictly_increasing all in
  map (@length Z) increasing.

(* Check if all elements in a list of nats are <= a given value *)
Fixpoint all_le (lens : list nat) (n : nat) : bool :=
  match lens with
  | [] => true
  | x :: xs => (x <=? n)%nat && all_le xs n
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition longestIncreasingSubsequence_precond_dec (nums : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition longestIncreasingSubsequence_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Binary search to find insertion position *)
Fixpoint binary_search_helper (sub : list Z) (num : Z) (left right : nat) (fuel : nat) : nat :=
  match fuel with
  | O => left
  | S fuel' =>
      if (left <? right)%nat then
        let mid := ((left + right) / 2)%nat in
        match nth_error sub mid with
        | None => left
        | Some mid_val =>
            if (mid_val =? num)%Z then right
            else if (mid_val <? num)%Z then
              binary_search_helper sub num (mid + 1)%nat right fuel'
            else
              binary_search_helper sub num left mid fuel'
        end
      else left
  end.

Definition binary_search (sub : list Z) (num : Z) : nat :=
  match sub with
  | [] => 0%nat
  | _ => binary_search_helper sub num 0%nat (length sub - 1)%nat (length sub)
  end.

(* Set element at index in list *)
Fixpoint set_at (l : list Z) (idx : nat) (val : Z) : list Z :=
  match l, idx with
  | [], _ => []
  | _ :: tl, O => val :: tl
  | hd :: tl, S n => hd :: set_at tl n val
  end.

(* Main loop processing each element *)
Fixpoint process_nums (nums : list Z) (sub : list Z) : list Z :=
  match nums with
  | [] => sub
  | num :: rest =>
      match sub with
      | [] => process_nums rest [num]
      | _ =>
          let last_idx := (length sub - 1)%nat in
          match nth_error sub last_idx with
          | None => process_nums rest sub
          | Some last_val =>
              if (last_val <? num)%Z then
                process_nums rest (sub ++ [num])
              else
                let pos := binary_search sub num in
                process_nums rest (set_at sub pos num)
          end
      end
  end.
(* !benchmark @end code_aux *)

Definition longestIncreasingSubsequence (nums : (list Z)) (h_precond : longestIncreasingSubsequence_precond nums) : Z :=
  (* !benchmark @start code *)
  match nums with
| [] => 0%Z
| hd :: tl => Z.of_nat (length (process_nums tl [hd]))
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition longestIncreasingSubsequence_postcond_dec (nums : list Z) (result : Z) : bool :=
  let lens := increasingSubseqLens nums in
  match lens with
  | [] => (result =? 0)%Z
  | _ => 
      let result_nat := Z.to_nat result in
      existsb (fun len => (len =? result_nat)%nat) lens &&
      all_le lens result_nat
  end.
(* !benchmark @end postcond_aux *)

Definition longestIncreasingSubsequence_postcond (nums : (list Z)) (result : Z) (h_precond : longestIncreasingSubsequence_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let lens := increasingSubseqLens nums in
In (Z.to_nat result) lens /\ Forall (fun len => (len <= Z.to_nat result)%nat) lens
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestIncreasingSubsequence_postcond_satisfied (nums : (list Z)) (h_precond : longestIncreasingSubsequence_precond nums) :
    longestIncreasingSubsequence_postcond nums (longestIncreasingSubsequence nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
