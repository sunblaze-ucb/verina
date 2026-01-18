(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zdiv.
Require Import Coq.Init.Nat.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition findMajorityElement_precond_dec (lst : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition findMajorityElement_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countOccurrences (n : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0%nat
  | x :: xs => if (x =? n)%Z then S (countOccurrences n xs) else countOccurrences n xs
  end.

Fixpoint find_majority_aux (candidates : list Z) (lst : list Z) (n : nat) : option Z :=
  match candidates with
  | [] => None
  | x :: xs => 
      let count := countOccurrences x lst in
      if Nat.ltb (n / 2)%nat count then Some x
      else find_majority_aux xs lst n
  end.
(* !benchmark @end code_aux *)

Definition findMajorityElement (lst : (list Z)) (h_precond : findMajorityElement_precond lst) : Z :=
  (* !benchmark @start code *)
  let n := length lst in
  match find_majority_aux lst lst n with
  | Some x => x
  | None => (-1)%Z
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition count_occurrences (x : Z) (lst : list Z) : nat :=
  length (filter (fun y => (y =? x)%Z) lst).

Definition findMajorityElement_postcond_dec (lst : list Z) (result : Z) : bool :=
  let count := fun x => count_occurrences x lst in
  let n := length lst in
  let majority := (andb (Nat.ltb (n / 2)%nat (count result))
                   (forallb (fun x => (orb (Nat.leb (count x) (n / 2)%nat) (x =? result)%Z)) lst)) in
  let all_minority := forallb (fun x => Nat.leb (count x) (n / 2)%nat) lst in
  if (result =? (-1))%Z then
    (orb all_minority majority)
  else
    majority.
(* !benchmark @end postcond_aux *)

Definition findMajorityElement_postcond (lst : (list Z)) (result : Z) (h_precond : findMajorityElement_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  let count := fun x => count_occurrences x lst in
  let n := length lst in
  let majority := (count result > (n / 2))%nat /\ Forall (fun x => (count x <= (n / 2))%nat \/ x = result) lst in
  (result = (-1)%Z -> Forall (fun x => (count x <= (n / 2))%nat) lst \/ majority) /\
  (result <> (-1)%Z -> majority)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findMajorityElement_postcond_satisfied (lst : (list Z)) (h_precond : findMajorityElement_precond lst) :
    findMajorityElement_postcond lst (findMajorityElement lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
