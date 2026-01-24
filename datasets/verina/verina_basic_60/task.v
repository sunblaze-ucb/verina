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
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition FindEvenNumbers_precond (arr : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint FindEvenNumbers_loop (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | h :: t => if isEven h then h :: FindEvenNumbers_loop t else FindEvenNumbers_loop t
  end.
(* !benchmark @end code_aux *)

Definition FindEvenNumbers (arr : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  FindEvenNumbers_loop arr
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint is_sublist (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], _ => true
  | _, [] => false
  | h1 :: t1, h2 :: t2 =>
      if (h1 =? h2)%Z then is_sublist t1 t2
      else is_sublist l1 t2
  end.

Fixpoint countP_Z (f : Z -> bool) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if f h then S (countP_Z f t) else countP_Z f t
  end.
(* !benchmark @end postcond_aux *)

Definition FindEvenNumbers_postcond (arr : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  forallb isEven result && is_sublist result arr && (length result =? countP_Z isEven arr)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem FindEvenNumbers_postcond_satisfied (arr : (list Z)) :
    FindEvenNumbers_precond arr = true ->
    FindEvenNumbers_postcond arr (FindEvenNumbers arr) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
