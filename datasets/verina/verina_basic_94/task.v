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

Definition iter_copy_precond (s : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint iter_copy_loop (s : list Z) (i : nat) (acc : list Z) : list Z :=
  match s with
  | [] => acc
  | h :: t => 
    match i with
    | O => iter_copy_loop t O (acc ++ [h])
    | S i' => iter_copy_loop t O (acc ++ [h])
    end
  end.
(* !benchmark @end code_aux *)

Definition iter_copy (s : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2)%Z && list_Z_eqb t1 t2
  | _, _ => false
  end.

Fixpoint all_elements_equal (s result : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' => 
    match nth_error s i', nth_error result i' with
    | Some v1, Some v2 => (v1 =? v2)%Z && all_elements_equal s result i'
    | _, _ => false
    end
  end.
(* !benchmark @end postcond_aux *)

Definition iter_copy_postcond (s : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length s =? length result)%nat) && all_elements_equal s result (length s)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem iter_copy_postcond_satisfied (s : (list Z)) :
    iter_copy_precond s = true ->
    iter_copy_postcond s (iter_copy s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
