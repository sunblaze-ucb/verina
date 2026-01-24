(* !benchmark @start import type=task *)
Require Import ZArith.
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

Definition isDivisibleBy11_precond (n : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition isDivisibleBy11 (n : Z) : bool :=
  (* !benchmark @start code *)
  (n mod 11 =? 0)%Z
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Check if there exists k such that n = 11 * k, which is equivalent to n mod 11 = 0 *)
Definition divisible_by_11 (n : Z) : bool := (n mod 11 =? 0)%Z.
(* !benchmark @end postcond_aux *)

Definition isDivisibleBy11_postcond (n : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  implb result (divisible_by_11 n) && implb (negb result) (negb (divisible_by_11 n))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isDivisibleBy11_postcond_satisfied (n : Z) :
    isDivisibleBy11_precond n = true ->
    isDivisibleBy11_postcond n (isDivisibleBy11 n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
