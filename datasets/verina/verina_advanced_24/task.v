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
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition lengthOfLIS_precond_dec (nums : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition lengthOfLIS_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint replace (l : list Z) (acc : list Z) (x : Z) : list Z :=
  match l with
  | [] => rev acc ++ [x]
  | y :: ys => if (x <=? y)%Z then rev acc ++ (x :: ys) else replace ys (y :: acc) x
  end.

Definition lisHelper (dp : list Z) (x : Z) : list Z :=
  replace dp [] x.
(* !benchmark @end code_aux *)

Definition lengthOfLIS (nums : (list Z)) (h_precond : lengthOfLIS_precond nums) : Z :=
  (* !benchmark @start code *)
  let finalDP := fold_left lisHelper nums [] in
  Z.of_nat (length finalDP)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint isStrictlyIncreasing (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <? y)%Z && isStrictlyIncreasing tl
  end.

Fixpoint subsequences (xs : list Z) : list (list Z) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
      let rest := subsequences xs' in
      rest ++ map (fun r => x :: r) rest
  end.

Definition lengthOfLIS_postcond_dec (nums : list Z) (result : Z) : bool :=
  let allIncreasing := filter (fun l => isStrictlyIncreasing l) (subsequences nums) in
  existsb (fun l => (Z.of_nat (length l) =? result)%Z) allIncreasing &&
  forallb (fun l => (Z.of_nat (length l) <=? result)%Z) allIncreasing.
(* !benchmark @end postcond_aux *)

Definition lengthOfLIS_postcond (nums : (list Z)) (result : Z) (h_precond : lengthOfLIS_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let isStrictlyIncreasing := fix isStrictlyIncreasing (l : list Z) : bool :=
    match l with
    | [] => true
    | [_] => true
    | x :: ((y :: _) as tl) => (x <? y)%Z && isStrictlyIncreasing tl
    end in
  let subsequences := fix subsequences (xs : list Z) : list (list Z) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
        let rest := subsequences xs' in
        rest ++ map (fun r => x :: r) rest
    end in
  let allIncreasing := filter (fun l => isStrictlyIncreasing l) (subsequences nums) in
  (exists l, In l allIncreasing /\ Z.of_nat (length l) = result) /\
  (forall l, In l allIncreasing -> (Z.of_nat (length l) <= result)%Z)
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
