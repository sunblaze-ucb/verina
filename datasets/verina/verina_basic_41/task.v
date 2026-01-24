(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition hasOnlyOneDistinctElement_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (firstElement : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => if (h =? firstElement)%Z then loop firstElement t else false
  end.
(* !benchmark @end code_aux *)

Definition hasOnlyOneDistinctElement (a : (list Z)) : bool :=
  (* !benchmark @start code *)
  match a with
  | [] => true
  | firstElement :: rest => loop firstElement rest
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_pairwise_eq (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: (h2 :: _) as t => (h1 =? h2)%Z && list_pairwise_eq t
  end.

Definition list_any_neq_first (l : list Z) : bool :=
  match l with
  | [] => false
  | first :: _ => existsb (fun x => negb (x =? first)%Z) l
  end.
(* !benchmark @end postcond_aux *)

Definition hasOnlyOneDistinctElement_postcond (a : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  implb result (list_pairwise_eq a) && implb (negb result) (list_any_neq_first a)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasOnlyOneDistinctElement_postcond_satisfied (a : (list Z)) :
    hasOnlyOneDistinctElement_precond a = true ->
    hasOnlyOneDistinctElement_postcond a (hasOnlyOneDistinctElement a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
