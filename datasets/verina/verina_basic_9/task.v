(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No additional solution helpers needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition hasCommonElement_precond_dec (a : list Z) (b : list Z) : bool :=
  (Nat.ltb 0%nat (length a)) && (Nat.ltb 0%nat (length b)).
(* !benchmark @end precond_aux *)

Definition hasCommonElement_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat /\ (length b > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_any {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if f x then true else list_any f xs
  end.
(* !benchmark @end code_aux *)

Definition hasCommonElement (a : (list Z)) (b : (list Z)) (h_precond : hasCommonElement_precond a b) : bool :=
  (* !benchmark @start code *)
  list_any (fun x => list_any (fun y => Z.eqb x y) b) a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition hasCommonElement_postcond_dec (a : list Z) (b : list Z) (result : bool) : bool :=
  let has_common := 
    list_any (fun x => list_any (fun y => Z.eqb x y) b) a
  in
  Bool.eqb result has_common.
(* !benchmark @end postcond_aux *)

Definition hasCommonElement_postcond (a : (list Z)) (b : (list Z)) (result : bool) (h_precond : hasCommonElement_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (exists i j, (i < length a)%nat /\ (j < length b)%nat /\ nth i a 0 = nth j b 0) <-> result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasCommonElement_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : hasCommonElement_precond a b) :
    hasCommonElement_postcond a b (hasCommonElement a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
