(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
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
Definition firstDuplicate_precond_dec (lst : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition firstDuplicate_precond (lst : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Fixpoint helper (seen : list Z) (rem : list Z) : option Z :=
  match rem with
  | [] => None
  | h :: t => 
      if existsb (Z.eqb h) seen then Some h 
      else helper (h :: seen) t
  end.
(* !benchmark @end code_aux *)

Definition firstDuplicate (lst : (list Z)) (h_precond : firstDuplicate_precond lst) : (option Z) :=
  (* !benchmark @start code *)
  helper [] lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Require Import Coq.Lists.List.
Import ListNotations.

(* Helper to check if a list has no duplicates *)
Fixpoint NoDup_bool {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (eqb x) xs) && NoDup_bool eqb xs
  end.

(* Count occurrences in a list *)
Fixpoint count_occ_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | y :: tl => if Z.eqb x y then S (count_occ_Z tl x) else count_occ_Z tl x
  end.

(* Filter list by predicate *)
Fixpoint filter_Z (f : Z -> bool) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter_Z f xs else filter_Z f xs
  end.

(* Head of list *)
Definition head_Z (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

Definition firstDuplicate_postcond_dec (lst : list Z) (result : option Z) : bool :=
  match result with
  | None => NoDup_bool Z.eqb lst
  | Some x => 
      let count_x := count_occ_Z lst x in
      let has_dup := (1 <? count_x)%nat in
      let filtered := filter_Z (fun y => (1 <? count_occ_Z lst y)%nat) lst in
      let first_dup := head_Z filtered in
      has_dup && match first_dup with
                 | Some y => Z.eqb x y
                 | None => false
                 end
  end.
(* !benchmark @end postcond_aux *)

Definition firstDuplicate_postcond (lst : (list Z)) (result : (option Z)) (h_precond : firstDuplicate_precond lst) : Prop :=
  (* !benchmark @start postcond *)
  match result with
| None => NoDup lst
| Some x =>
    (count_occ_Z lst x > 1)%nat /\
    head_Z (filter_Z (fun y => (1 <? count_occ_Z lst y)%nat) lst) = Some x
end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem firstDuplicate_postcond_satisfied (lst : (list Z)) (h_precond : firstDuplicate_precond lst) :
    firstDuplicate_postcond lst (firstDuplicate lst h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
