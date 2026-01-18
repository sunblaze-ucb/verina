(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution-level helpers *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition mostFrequent_precond_dec (xs : list Z) : bool :=
  match xs with
  | [] => false
  | _ => true
  end.
(* !benchmark @end precond_aux *)

Definition mostFrequent_precond (xs : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  xs <> []
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to count occurrences of x in xs *)
Fixpoint count (xs : list Z) (x : Z) : nat :=
  match xs with
  | [] => 0%nat
  | (h :: t) => if (h =? x)%Z then S (count t x) else count t x
  end.

(* Get frequency for each element in the list *)
Fixpoint getFrequencies (xs : list Z) : list (Z * nat) :=
  match xs with
  | [] => []
  | (h :: t) => (h, count xs h) :: getFrequencies t
  end.

(* Get maximum frequency from frequency list *)
Fixpoint maxFreq (freqs : list (Z * nat)) : nat :=
  match freqs with
  | [] => 0%nat
  | ((_, f) :: t) => Nat.max f (maxFreq t)
  end.

(* Find first element with given frequency *)
Fixpoint findFirstWithFreq (xs : list Z) (freqs : list (Z * nat)) (target : nat) : Z :=
  match xs with
  | [] => 0
  | (h :: t) => 
      match freqs with
      | [] => 0
      | ((x, f) :: ft) =>
          if (h =? x)%Z then
            if Nat.eqb f target then h
            else findFirstWithFreq t ft target
          else findFirstWithFreq xs ft target
      end
  end.

(* Simplified version: find first element in xs with maximum frequency *)
Fixpoint findMostFrequent (xs original : list Z) (maxF : nat) : Z :=
  match xs with
  | [] => 0
  | (h :: t) => if Nat.eqb (count original h) maxF then h else findMostFrequent t original maxF
  end.
(* !benchmark @end code_aux *)

Definition mostFrequent (xs : (list Z)) (h_precond : mostFrequent_precond xs) : Z :=
  (* !benchmark @start code *)
  let freqs := getFrequencies xs in
let maxF := maxFreq freqs in
findMostFrequent xs xs maxF
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to check if x is in list *)
Fixpoint inList (x : Z) (xs : list Z) : bool :=
  match xs with
  | [] => false
  | (h :: t) => if (h =? x)%Z then true else inList x t
  end.

(* Helper to check if all elements satisfy property *)
Fixpoint allSatisfy (xs : list Z) (original : list Z) (maxCount : nat) : bool :=
  match xs with
  | [] => true
  | (h :: t) => (count original h <=? maxCount)%nat && allSatisfy t original maxCount
  end.

(* Helper to filter elements with target count *)
Fixpoint filterByCount (xs original : list Z) (target : nat) : list Z :=
  match xs with
  | [] => []
  | (h :: t) => if Nat.eqb (count original h) target 
                then h :: filterByCount t original target
                else filterByCount t original target
  end.

(* Helper to get head of filtered list *)
Definition headOption (xs : list Z) : option Z :=
  match xs with
  | [] => None
  | (h :: _) => Some h
  end.

Definition mostFrequent_postcond_dec (xs : list Z) (result : Z) : bool :=
  let resultCount := count xs result in
  inList result xs &&
  allSatisfy xs xs resultCount &&
  match headOption (filterByCount xs xs resultCount) with
  | Some x => (x =? result)%Z
  | None => false
  end.
(* !benchmark @end postcond_aux *)

Definition mostFrequent_postcond (xs : (list Z)) (result : Z) (h_precond : mostFrequent_precond xs) : Prop :=
  (* !benchmark @start postcond *)
  let countFn := fun x => count xs x in
In result xs /\
Forall (fun x => (countFn x <= countFn result)%nat) xs /\
match headOption (filterByCount xs xs (countFn result)) with
| Some x => x = result
| None => False
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mostFrequent_postcond_satisfied (xs : (list Z)) (h_precond : mostFrequent_precond xs) :
    mostFrequent_postcond xs (mostFrequent xs h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
