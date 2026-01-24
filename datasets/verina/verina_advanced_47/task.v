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

Definition mergeIntervals_precond (intervals : (list (Z * Z))) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert (x : Z * Z) (sorted : list (Z * Z)) : list (Z * Z) :=
  match sorted with
  | [] => [x]
  | y :: ys => if (fst x <=? fst y)%Z then x :: sorted else y :: insert x ys
  end.

Fixpoint sort_intervals (xs : list (Z * Z)) : list (Z * Z) :=
  match xs with
  | [] => []
  | x :: xs' => insert x (sort_intervals xs')
  end.

Fixpoint merge_helper (xs : list (Z * Z)) (acc : list (Z * Z)) : list (Z * Z) :=
  match xs, acc with
  | [], _ => rev acc
  | (s, e) :: rest, [] => merge_helper rest [(s, e)]
  | (s, e) :: rest, (ps, pe) :: accTail =>
    if (s <=? pe)%Z then
      merge_helper rest ((ps, Z.max pe e) :: accTail)
    else
      merge_helper rest ((s, e) :: (ps, pe) :: accTail)
  end.
(* !benchmark @end code_aux *)

Definition mergeIntervals (intervals : (list (Z * Z))) : (list (Z * Z)) :=
  (* !benchmark @start code *)
  merge_helper (sort_intervals intervals) []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition interval_covers (interval : Z * Z) (rs re : Z) : bool :=
  (rs <=? fst interval)%Z && (snd interval <=? re)%Z.

Definition is_covered (interval : Z * Z) (result : list (Z * Z)) : bool :=
  existsb (fun r => interval_covers interval (fst r) (snd r)) result.

Fixpoint noOverlap (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | [_] => true
  | (_, e1) :: ((s2, e2) :: rest) as tail => (e1 <? s2)%Z && noOverlap tail
  end.
(* !benchmark @end postcond_aux *)

Definition mergeIntervals_postcond (intervals : (list (Z * Z))) (result : (list (Z * Z))) : bool :=
  (* !benchmark @start postcond *)
  forallb (fun interval => is_covered interval result) intervals && noOverlap result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mergeIntervals_postcond_satisfied (intervals : (list (Z * Z))) :
    mergeIntervals_precond intervals = true ->
    mergeIntervals_postcond intervals (mergeIntervals intervals) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
