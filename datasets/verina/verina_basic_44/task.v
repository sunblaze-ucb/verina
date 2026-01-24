(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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

Definition isOddAtIndexOdd_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isOdd (n : Z) : bool :=
  (n mod 2 =? 1)%Z.

Fixpoint checkOddAtOddIdx (l : list Z) (idx : nat) : bool :=
  match l with
  | [] => true
  | x :: xs => 
    let idxOdd := isOdd (Z.of_nat idx) in
    let xOdd := isOdd x in
    (implb idxOdd xOdd) && checkOddAtOddIdx xs (S idx)
  end.
(* !benchmark @end code_aux *)

Definition isOddAtIndexOdd (a : (list Z)) : bool :=
  (* !benchmark @start code *)
  checkOddAtOddIdx a 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isOdd_post (n : Z) : bool :=
  (n mod 2 =? 1)%Z.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint check_all_odd_indices (a : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' => 
    let check_i' := 
      implb ((i' <? length a)%nat && isOdd_post (Z.of_nat i'))
            (isOdd_post (nth_Z a i'))
    in check_i' && check_all_odd_indices a i'
  end.
(* !benchmark @end postcond_aux *)

Definition isOddAtIndexOdd_postcond (a : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb result (check_all_odd_indices a (length a))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isOddAtIndexOdd_postcond_satisfied (a : (list Z)) :
    isOddAtIndexOdd_precond a = true ->
    isOddAtIndexOdd_postcond a (isOddAtIndexOdd a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
