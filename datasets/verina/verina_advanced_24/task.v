(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
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

Definition lengthOfLIS_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint replace_in_dp (l : list Z) (acc : list Z) (x : Z) : list Z :=
  match l with
  | [] => rev acc ++ [x]
  | y :: ys => if (x <=? y)%Z then rev acc ++ (x :: ys) else replace_in_dp ys (y :: acc) x
  end.

Definition lisHelper (dp : list Z) (x : Z) : list Z :=
  replace_in_dp dp [] x.
(* !benchmark @end code_aux *)

Definition lengthOfLIS (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  Z.of_nat (length (fold_left lisHelper nums []))
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint isStrictlyIncreasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: rest) as tail) => (x <? y)%Z && isStrictlyIncreasing tail
  end.

Fixpoint subsequences (xs : list Z) : list (list Z) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let rest := subsequences xs' in
    rest ++ map (fun r => x :: r) rest
  end.

Definition allIncreasingSubseqs (nums : list Z) : list (list Z) :=
  filter (fun l => isStrictlyIncreasing l) (subsequences nums).

Definition anyHasLength (subs : list (list Z)) (n : Z) : bool :=
  existsb (fun l => (Z.of_nat (length l) =? n)%Z) subs.

Definition allHaveLengthLE (subs : list (list Z)) (n : Z) : bool :=
  forallb (fun l => (Z.of_nat (length l) <=? n)%Z) subs.
(* !benchmark @end postcond_aux *)

Definition lengthOfLIS_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let allIncreasing := allIncreasingSubseqs nums in
  anyHasLength allIncreasing result && allHaveLengthLE allIncreasing result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lengthOfLIS_postcond_satisfied (nums : (list Z)) :
    lengthOfLIS_precond nums = true ->
    lengthOfLIS_postcond nums (lengthOfLIS nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
