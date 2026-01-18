(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Count occurrences of an element in a list *)
Fixpoint count_occ (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eqb h x then S (count_occ t x) else count_occ t x
  end.

(* Check if any element satisfies a predicate *)
Fixpoint any (l : list Z) (p : Z -> bool) : bool :=
  match l with
  | [] => false
  | h :: t => if p h then true else any t p
  end.

(* Build a list of (element, count) pairs *)
Fixpoint count_all_helper (l : list Z) (seen : list Z) : list (Z * nat) :=
  match l with
  | [] => []
  | h :: t => 
      if existsb (Z.eqb h) seen 
      then count_all_helper t seen
      else (h, count_occ l h) :: count_all_helper t (h :: seen)
  end.

Definition count_all (l : list Z) : list (Z * nat) :=
  count_all_helper l [].

(* Find first element satisfying predicate *)
Fixpoint find_first {A : Type} (l : list A) (p : A -> bool) : option A :=
  match l with
  | [] => None
  | h :: t => if p h then Some h else find_first t p
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition majorityElement_precond_dec (nums : list Z) : bool :=
  let n := length nums in
  match n with
  | O => false
  | S _ => any nums (fun x => Nat.ltb (n / 2)%nat (count_occ nums x))
  end.
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length nums > 0)%nat /\ any nums (fun x => Nat.ltb (length nums / 2)%nat (count_occ nums x)) = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code helpers needed *)
(* !benchmark @end code_aux *)

Definition majorityElement (nums : (list Z)) (h_precond : majorityElement_precond nums) : Z :=
  (* !benchmark @start code *)
  let counts := count_all nums in
  let n := length nums in
  match find_first counts (fun p => Nat.ltb (n / 2)%nat (snd p)) with
  | Some (k, _) => k
  | None => 0%Z
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition majorityElement_postcond_dec (nums : list Z) (result : Z) : bool :=
  let n := length nums in
  andb (Nat.ltb (n / 2)%nat (count_occ nums result))
       (forallb (fun x => orb (Z.eqb x result) (Nat.leb (count_occ nums x) (n / 2)%nat)) nums).
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (nums : (list Z)) (result : Z) (h_precond : majorityElement_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  let n := length nums in
  (count_occ nums result > n / 2)%nat /\
  (forall x, In x nums -> x <> result -> (count_occ nums x <= n / 2)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (nums : (list Z)) (h_precond : majorityElement_precond nums) :
    majorityElement_postcond nums (majorityElement nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
