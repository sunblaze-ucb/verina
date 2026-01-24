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

Definition Find_precond (a : (list Z)) (key : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint search (a : list Z) (key : Z) (index : nat) : Z :=
  match a with
  | [] => -1
  | h :: t => if (h =? key)%Z then Z.of_nat index
              else search t key (S index)
  end.
(* !benchmark @end code_aux *)

Definition Find (a : (list Z)) (key : Z) : Z :=
  (* !benchmark @start code *)
  search a key O
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_Z t n' default
              end
  end.

Fixpoint all_before_not_eq (a : list Z) (key : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => all_before_not_eq a key n' && negb (nth_Z a n' 0 =? key)%Z
  end.

Fixpoint all_not_eq (a : list Z) (key : Z) : bool :=
  match a with
  | [] => true
  | h :: t => negb (h =? key)%Z && all_not_eq t key
  end.
(* !benchmark @end postcond_aux *)

Definition Find_postcond (a : (list Z)) (key : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  ((result =? -1)%Z || ((result >=? 0)%Z && (result <? Z.of_nat (length a))%Z))
  && implb (negb (result =? -1)%Z) 
           ((nth_Z a (Z.to_nat result) 0 =? key)%Z && all_before_not_eq a key (Z.to_nat result))
  && implb (result =? -1)%Z (all_not_eq a key)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Find_postcond_satisfied (a : (list Z)) (key : Z) :
    Find_precond a key = true ->
    Find_postcond a key (Find a key) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
