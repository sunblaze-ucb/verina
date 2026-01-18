(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import List.
Require Import ZArith.
Require Import Bool.
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
Definition lengthOfLIS_precond_dec (nums : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition lengthOfLIS_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxInList (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => maxInList xs (if (x <=? acc)%nat then acc else x)
  end.

Definition maxInArray (arr : list nat) : nat :=
  maxInList arr 0%nat.

Fixpoint dp_inner_loop (nums : list Z) (dp : list nat) (i j : nat) : list nat :=
  match j with
  | O => match nth_error nums O, nth_error nums i, nth_error dp O, nth_error dp i with
         | Some nj, Some ni, Some dpj, Some dpi =>
           if (nj <? ni)%Z && (dpi <? dpj + 1)%nat
           then (firstn i dp) ++ [(dpj + 1)%nat] ++ (skipn (i + 1) dp)
           else dp
         | _, _, _, _ => dp
         end
  | S j' => 
      let dp' := dp_inner_loop nums dp i j' in
      match nth_error nums j, nth_error nums i, nth_error dp' j, nth_error dp' i with
      | Some nj, Some ni, Some dpj, Some dpi =>
          if (nj <? ni)%Z && (dpi <? dpj + 1)%nat
          then (firstn i dp') ++ [(dpj + 1)%nat] ++ (skipn (i + 1) dp')
          else dp'
      | _, _, _, _ => dp'
      end
  end.

Fixpoint dp_outer_loop (nums : list Z) (dp : list nat) (i n : nat) : list nat :=
  match i with
  | O => dp
  | S i' => 
      let dp' := dp_outer_loop nums dp i' n in
      if (i' + 1 <? n)%nat
      then dp_inner_loop nums dp' i' i'
      else dp'
  end.
(* !benchmark @end code_aux *)

Definition lengthOfLIS (nums : (list Z)) (h_precond : lengthOfLIS_precond nums) : nat :=
  (* !benchmark @start code *)
  match nums with
| [] => 0%nat
| _ => let n := length nums in
       let init_dp := repeat 1%nat n in
       let final_dp := dp_outer_loop nums init_dp (n - 1) n in
       maxInArray final_dp
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_subsequences (l : list Z) : list (list Z) :=
  match l with
  | [] => [[]]
  | x :: xs =>
      let subs := all_subsequences xs in
      subs ++ (map (fun sub => x :: sub) subs)
  end.

Fixpoint is_strictly_increasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _) as tl =>
      (x <? y)%Z && is_strictly_increasing tl
  end.

Definition lengthOfLIS_postcond_dec (nums : list Z) (result : nat) : bool :=
  let allSubseq := all_subsequences nums in
  let increasingSubseq := filter is_strictly_increasing allSubseq in
  let lengths := map (@length Z) increasingSubseq in
  existsb (Nat.eqb result) lengths &&
  forallb (fun len => len <=? result) lengths.
(* !benchmark @end postcond_aux *)

Definition lengthOfLIS_postcond (nums : (list Z)) (result : nat) (h_precond : lengthOfLIS_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let allSubseq := all_subsequences nums in
let increasingSubseq := filter is_strictly_increasing allSubseq in
let lengths := map (@length Z) increasingSubseq in
In result lengths /\ Forall (fun len => (len <= result)%nat) lengths
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lengthOfLIS_postcond_satisfied (nums : (list Z)) (h_precond : lengthOfLIS_precond nums) :
    lengthOfLIS_postcond nums (lengthOfLIS nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
