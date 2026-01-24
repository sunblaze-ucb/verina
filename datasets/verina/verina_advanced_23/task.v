(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import Bool.
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

Definition isPowerOfTwo_precond (n : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isPowerOfTwo_aux (m : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (m =? 1)%Z then true
    else if negb ((m mod 2) =? 0)%Z then false
    else isPowerOfTwo_aux (m / 2) fuel'
  end.
(* !benchmark @end code_aux *)

Definition isPowerOfTwo (n : Z) : bool :=
  (* !benchmark @start code *)
  if (n <=? 0)%Z then false
  else isPowerOfTwo_aux n (Z.to_nat n)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint pow2 (exp : nat) : Z :=
  match exp with
  | O => 1
  | S n => 2 * pow2 n
  end.

Fixpoint existsb_nat (f : nat -> bool) (fuel : nat) : bool :=
  match fuel with
  | O => f O
  | S n' => f fuel || existsb_nat f n'
  end.

Definition exists_pow2_eq (n : Z) (limit : nat) : bool :=
  existsb_nat (fun x => (pow2 x =? n)%Z && (n >? 0)%Z) limit.
(* !benchmark @end postcond_aux *)

Definition isPowerOfTwo_postcond (n : Z) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let limit := Z.to_nat (Z.abs n + 1) in
  implb result (exists_pow2_eq n limit) &&
  implb (negb result) (negb (exists_pow2_eq n limit))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPowerOfTwo_postcond_satisfied (n : Z) :
    isPowerOfTwo_precond n = true ->
    isPowerOfTwo_postcond n (isPowerOfTwo n) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
