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

Definition moveZeroes_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition moveZeroes_impl (xs : list Z) : list Z :=
  let nonzeros := filter (fun x => negb (x =? 0)) xs in
  let zeros := filter (fun x => x =? 0) xs in
  nonzeros ++ zeros.
(* !benchmark @end code_aux *)

Definition moveZeroes (xs : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  moveZeroes_impl xs
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint countVal (val : Z) (xs : list Z) : nat :=
  match xs with
  | [] => O
  | x :: rest =>
    let r := countVal val rest in
    if (x =? val) then S r else r
  end.

Fixpoint isSubsequence (xs ys : list Z) : bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if (x =? y) then isSubsequence xt yt else isSubsequence xs yt
  end.

Fixpoint dropWhile (f : Z -> bool) (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest => if f x then dropWhile f rest else (x :: rest)
  end.
(* !benchmark @end postcond_aux *)

Definition moveZeroes_postcond (xs : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  isSubsequence (filter (fun x => negb (x =? 0)) xs) result &&
  forallb (fun x => x =? 0) (dropWhile (fun x => negb (x =? 0)) result) &&
  (countVal 0 xs =? countVal 0 result)%nat &&
  (length xs =? length result)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem moveZeroes_postcond_satisfied (xs : (list Z)) :
    moveZeroes_precond xs = true ->
    moveZeroes_postcond xs (moveZeroes xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
