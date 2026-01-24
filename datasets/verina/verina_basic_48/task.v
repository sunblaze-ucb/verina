(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition isPerfectSquare_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPerfectSquare_check (x : nat) (n : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (n <? x * x)%nat then false
    else if (x * x =? n)%nat then true
    else isPerfectSquare_check (x + 1)%nat n fuel'
  end.
(* !benchmark @end code_aux *)

Definition isPerfectSquare (n : nat) : bool :=
  (* !benchmark @start code *)
  if (n =? 0)%nat then true
  else isPerfectSquare_check 1 n n
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint existsPerfectSquareRoot (i : nat) (n : nat) : bool :=
  match i with
  | O => (0 =? n)%nat
  | S i' => if (i * i =? n)%nat then true else existsPerfectSquareRoot i' n
  end.
(* !benchmark @end postcond_aux *)

Definition isPerfectSquare_postcond (n : nat) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb result (existsPerfectSquareRoot n n)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPerfectSquare_postcond_satisfied (n : nat) :
    isPerfectSquare_precond n = true ->
    isPerfectSquare_postcond n (isPerfectSquare n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
