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

Definition arraySum_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t
  end.
(* !benchmark @end code_aux *)

Definition arraySum (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  list_sum a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sumTo (a : list Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => sumTo a n' + nth n' a 0
  end.
(* !benchmark @end postcond_aux *)

Definition arraySum_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  ((result - sumTo a (length a) =? 0) && (result >=? sumTo a (length a)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem arraySum_postcond_satisfied (a : (list Z)) :
    arraySum_precond a = true ->
    arraySum_postcond a (arraySum a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
