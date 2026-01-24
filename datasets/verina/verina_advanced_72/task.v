(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition singleDigitPrimeFactor_precond (n : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition singleDigitPrimeFactor (n : nat) : nat :=
  (* !benchmark @start code *)
  if n =? 0 then 0
  else if n mod 2 =? 0 then 2
  else if n mod 3 =? 0 then 3
  else if n mod 5 =? 0 then 5
  else if n mod 7 =? 0 then 7
  else 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Definition in_list_nat (x : nat) (l : list nat) : bool :=
  existsb (fun y => (x =? y)%nat) l.

Definition all_smaller_primes_dont_divide (n : nat) (p : nat) : bool :=
  forallb (fun x => implb (in_list_nat x [2; 3; 5; 7]) (negb (n mod x =? 0)%nat)) (seq 0 p).
(* !benchmark @end postcond_aux *)

Definition singleDigitPrimeFactor_postcond (n : nat) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  in_list_nat result [0; 2; 3; 5; 7] &&
  implb (result =? 0)%nat ((n =? 0)%nat || forallb (fun p => negb (n mod p =? 0)%nat) [2; 3; 5; 7]) &&
  implb (negb (result =? 0)%nat) (negb (n =? 0)%nat && (n mod result =? 0)%nat && all_smaller_primes_dont_divide n result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem singleDigitPrimeFactor_postcond_satisfied (n : nat) :
    singleDigitPrimeFactor_precond n = true ->
    singleDigitPrimeFactor_postcond n (singleDigitPrimeFactor n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
