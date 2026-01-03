(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition findExponents_precond_dec (n : nat) (primes : (list nat)) : bool := true.
(* !benchmark @end precond_aux *)

Definition findExponents_precond (n : nat) (primes : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findExponents (n : nat) (primes : (list nat)) (h_precond : findExponents_precond n primes) : (list (nat  * nat)) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition findExponents_postcond_dec (n : nat) (primes : (list nat)) (result : (list (nat  * nat))) : bool := true.
(* !benchmark @end postcond_aux *)

Definition findExponents_postcond (n : nat) (primes : (list nat)) (result : (list (nat  * nat))) (h_precond : findExponents_precond n primes) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem findExponents_postcond_satisfied (n : nat) (primes : (list nat)) (h_precond : findExponents_precond n primes) :
    findExponents_postcond n primes (findExponents n primes h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
