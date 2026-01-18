(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
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
Definition mergeIntervals_precond_dec (intervals : list (Z * Z)) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition mergeIntervals_precond (intervals : (list (Z * Z))) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Insertion sort based on the start of intervals *)
Fixpoint insert (x : Z * Z) (sorted : list (Z * Z)) : list (Z * Z) :=
  match sorted with
  | [] => [x]
  | y :: ys => if (fst x <=? fst y)%Z then x :: sorted else y :: insert x ys
  end.

Fixpoint sort (xs : list (Z * Z)) : list (Z * Z) :=
  match xs with
  | [] => []
  | x :: xs' => insert x (sort xs')
  end.

(* Merge sorted intervals *)
Fixpoint merge (xs : list (Z * Z)) (acc : list (Z * Z)) : list (Z * Z) :=
  match xs, acc with
  | [], _ => rev acc
  | (s, e) :: rest, [] => merge rest [(s, e)]
  | (s, e) :: rest, (ps, pe) :: accTail =>
      if (s <=? pe)%Z then
        merge rest ((ps, Z.max pe e) :: accTail)
      else
        merge rest ((s, e) :: (ps, pe) :: accTail)
  end.
(* !benchmark @end code_aux *)

Definition mergeIntervals (intervals : (list (Z * Z))) (h_precond : mergeIntervals_precond intervals) : (list (Z * Z)) :=
  (* !benchmark @start code *)
  let sorted := sort intervals in
  merge sorted []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Check that all original intervals are covered by some result interval *)
Fixpoint covered_helper (intervals result : list (Z * Z)) : bool :=
  forallb (fun '(s, e) =>
    existsb (fun '(rs, re) => andb (rs <=? s)%Z (e <=? re)%Z) result
  ) intervals.

(* Check that no intervals in the result overlap *)
Fixpoint noOverlap (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | [_] => true
  | (_, e1) :: ((s2, e2) :: _  as l0) => andb (e1 <? s2)%Z (noOverlap l0)
  end.

Definition mergeIntervals_postcond_dec (intervals result : list (Z * Z)) : bool :=
  andb (covered_helper intervals result) (noOverlap result).
(* !benchmark @end postcond_aux *)

Definition mergeIntervals_postcond (intervals : (list (Z * Z))) (result : (list (Z * Z))) (h_precond : mergeIntervals_precond intervals) : Prop :=
  (* !benchmark @start postcond *)
  let covered := forallb (fun '(s, e) =>
  existsb (fun '(rs, re) => andb (rs <=? s)%Z (e <=? re)%Z) result
) intervals in
covered = true /\ noOverlap result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeIntervals_postcond_satisfied (intervals : (list (Z * Z))) (h_precond : mergeIntervals_precond intervals) :
    mergeIntervals_postcond intervals (mergeIntervals intervals h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
