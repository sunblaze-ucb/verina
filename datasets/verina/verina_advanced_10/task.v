(* !benchmark @start import type=task *)
Require Import Bool.
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
Fixpoint is_prime_helper (n k : nat) : bool :=
  match k with
  | O => true
  | S O => true
  | S k' => if (n mod k =? O)%nat then false else is_prime_helper n k'
  end.

Definition is_prime (n : nat) : bool :=
  match n with
  | O => false
  | S O => false
  | S (S _) => is_prime_helper n (n - 1)
  end.

Fixpoint nodup_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (fun y => (y =? x)%nat) xs) && nodup_nat xs
  end.
(* !benchmark @end precond_aux *)

Definition findExponents_precond (n : nat) (primes : (list nat)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? n)%nat && (1 <=? length primes)%nat && forallb is_prime primes && nodup_nat primes
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countFactor (fuel : nat) (n p count : nat) : nat * nat :=
  match fuel with
  | O => (count, n)
  | S fuel' =>
    match n with
    | O => (count, O)
    | _ =>
      if (1 <=? n)%nat && (2 <=? p)%nat then
        if (n mod p =? O)%nat then
          countFactor fuel' (n / p) p (count + 1)%nat
        else
          (count, n)
      else
        (count, n)
    end
  end.

Fixpoint countFactors (fuel : nat) (n : nat) (primes : list nat) : list (nat * nat) :=
  match primes with
  | [] => []
  | p :: ps =>
    let result := countFactor fuel n p O in
    let count := fst result in
    let n' := snd result in
    (p, count) :: countFactors fuel n' ps
  end.
(* !benchmark @end code_aux *)

Definition findExponents (n : nat) (primes : (list nat)) : (list (nat  * nat)) :=
  (* !benchmark @start code *)
  countFactors n n primes
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint foldl_product (l : list (nat * nat)) (acc : nat) : nat :=
  match l with
  | [] => acc
  | (p, e) :: rest => foldl_product rest (acc * Nat.pow p e)%nat
  end.

Fixpoint list_nat_mem (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => (x =? y)%nat || list_nat_mem x ys
  end.
(* !benchmark @end postcond_aux *)

Definition findExponents_postcond (n : nat) (primes : (list nat)) (result : (list (nat  * nat))) : bool :=
  (* !benchmark @start postcond *)
  (n =? foldl_product result 1)%nat &&
  forallb (fun pair => list_nat_mem (fst pair) primes) result &&
  forallb (fun p => existsb (fun pair => (fst pair =? p)%nat) result) primes
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findExponents_postcond_satisfied (n : nat) (primes : (list nat)) :
    findExponents_precond n primes = true ->
    findExponents_postcond n primes (findExponents n primes) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
