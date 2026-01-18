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
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* additional helper definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition dissimilarElements_precond_dec (a : list Z) (b : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition dissimilarElements_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint inList (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | h :: t => if Z.eqb h x then true else inList t x
  end.

Fixpoint removeDuplicates (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if inList t h then removeDuplicates t else h :: removeDuplicates t
  end.

Fixpoint insertSorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if (x <=? h)%Z then x :: l else h :: insertSorted x t
  end.

Fixpoint insertionSort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insertSorted h (insertionSort t)
  end.

Fixpoint filterNotInList (l : list Z) (exclude : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if inList exclude h then filterNotInList t exclude else h :: filterNotInList t exclude
  end.
(* !benchmark @end code_aux *)

Definition dissimilarElements (a : (list Z)) (b : (list Z)) (h_precond : dissimilarElements_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  let elements_in_a_not_b := filterNotInList a b in
  let elements_in_b_not_a := filterNotInList b a in
  let combined := elements_in_a_not_b ++ elements_in_b_not_a in
  let unique := removeDuplicates combined in
  insertionSort unique
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allb_Z (f : Z -> bool) (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => andb (f h) (allb_Z f t)
  end.

Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => 
      match t with
      | [] => true
      | h2 :: t' => andb (h <=? h2)%Z (is_sorted t)
      end
  end.

Fixpoint has_no_duplicates (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => andb (negb (inList t h)) (has_no_duplicates t)
  end.

Definition dissimilarElements_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  let all_dissimilar := allb_Z (fun x => xorb (inList a x) (inList b x)) result in
  let sorted := is_sorted result in
  let no_dups := has_no_duplicates result in
  let a_check := allb_Z (fun x => if inList b x then negb (inList result x) else inList result x) a in
  let b_check := allb_Z (fun x => if inList a x then negb (inList result x) else inList result x) b in
  andb all_dissimilar (andb sorted (andb no_dups (andb a_check b_check))).
(* !benchmark @end postcond_aux *)

Definition dissimilarElements_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : dissimilarElements_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (forall x : Z, In x result -> inList a x <> inList b x) /\
  StronglySorted Z.le result /\
  (forall x : Z, In x a -> (if inList b x then ~In x result else In x result)) /\
  (forall x : Z, In x b -> (if inList a x then ~In x result else In x result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem dissimilarElements_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : dissimilarElements_precond a b) :
    dissimilarElements_postcond a b (dissimilarElements a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
