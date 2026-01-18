(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Helper to check if a number is prime *)
Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall m : nat, m > 1 -> m < p -> ~(exists k, p = m * k).

Definition is_prime_dec (p : nat) : bool :=
  (p >? 1).

(* Helper to check if all elements satisfy a predicate *)
Fixpoint all {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => f x && all f xs
  end.

(* Helper to check for duplicates in list *)
Fixpoint nodup {A : Type} (eq_dec : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (eq_dec x) xs) && nodup eq_dec xs
  end.

Definition findExponents_precond_dec (n : nat) (primes : list nat) : bool :=
  (n >? 0) && (length primes >? 0) && all (fun p => is_prime_dec p) primes && nodup Nat.eqb primes.
(* !benchmark @end precond_aux *)

Definition findExponents_precond (n : nat) (primes : (list nat)) : Prop :=
  (* !benchmark @start precond *)
  n > 0 /\
length primes > 0 /\
(forall p, In p primes -> is_prime p) /\
NoDup primes
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to count how many times p divides n *)
Fixpoint countFactor (fuel n p : nat) (count : nat) : (nat * nat) :=
  match fuel with
  | O => (count, n)
  | S fuel' =>
      if (n >? 0) && (p >? 1) then
        if Nat.eqb (n mod p) 0 then
          countFactor fuel' (n / p) p (count + 1)
        else
          (count, n)
      else
        (count, n)
  end.

(* Main recursive function to process list of primes *)
Fixpoint countFactors (fuel : nat) (n : nat) (primes : list nat) : list (nat * nat) :=
  match primes with
  | [] => []
  | p :: ps =>
      let '(count, n') := countFactor fuel n p 0 in
      (p, count) :: countFactors fuel n' ps
  end.
(* !benchmark @end code_aux *)

Definition findExponents (n : nat) (primes : (list nat)) (h_precond : findExponents_precond n primes) : (list (nat  * nat)) :=
  (* !benchmark @start code *)
  countFactors n n primes
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if element exists in list *)
Fixpoint mem_nat (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => Nat.eqb x y || mem_nat x ys
  end.

(* Helper to check if any element satisfies predicate *)
Fixpoint any {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => f x || any f xs
  end.

(* Helper to compute fold left *)
Fixpoint fold_left_nat (f : nat -> nat * nat -> nat) (l : list (nat * nat)) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => fold_left_nat f xs (f acc x)
  end.

Definition findExponents_postcond_dec (n : nat) (primes : list nat) (result : list (nat * nat)) : bool :=
  let reconstructed := fold_left_nat (fun acc '(p, e) => acc * (p ^ e)) result 1 in
  (Nat.eqb n reconstructed) &&
  all (fun '(p, _) => mem_nat p primes) result &&
  all (fun p => any (fun '(p', _) => Nat.eqb p' p) result) primes.
(* !benchmark @end postcond_aux *)

Definition findExponents_postcond (n : nat) (primes : (list nat)) (result : (list (nat  * nat))) (h_precond : findExponents_precond n primes) : Prop :=
  (* !benchmark @start postcond *)
  (n = fold_left (fun acc '(p, e) => acc * (p ^ e)) result 1%nat) /\
(forall p e, In (p, e) result -> In p primes) /\
(forall p, In p primes -> exists e, In (p, e) result)
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
