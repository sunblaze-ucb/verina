(* !benchmark @start import type=task *)
Require Import Bool.
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
Definition hasOnlyOneDistinctElement_precond_dec (a : list Z) : bool :=
  match length a with
  | O => false
  | S _ => true
  end.
(* !benchmark @end precond_aux *)

Definition hasOnlyOneDistinctElement_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length a > 0)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint hasOnlyOneDistinctElement_loop (firstElement : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => if (x =? firstElement)%Z then hasOnlyOneDistinctElement_loop firstElement xs else false
  end.
(* !benchmark @end code_aux *)

Definition hasOnlyOneDistinctElement (a : (list Z)) (h_precond : hasOnlyOneDistinctElement_precond a) : bool :=
  (* !benchmark @start code *)
  match a with
  | [] => true
  | firstElement :: rest => hasOnlyOneDistinctElement_loop firstElement rest
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_equal (l : list Z) (x : Z) : Prop :=
  match l with
  | [] => True
  | y :: ys => y = x /\ all_equal ys x
  end.

Fixpoint any_different (l : list Z) (x : Z) : Prop :=
  match l with
  | [] => False
  | y :: ys => y <> x \/ any_different ys x
  end.

Fixpoint all_equal_dec (l : list Z) (x : Z) : bool :=
  match l with
  | [] => true
  | y :: ys => if (y =? x)%Z then all_equal_dec ys x else false
  end.

Fixpoint any_different_dec (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | y :: ys => if negb (y =? x)%Z then true else any_different_dec ys x
  end.

Definition hasOnlyOneDistinctElement_postcond_dec (a : list Z) (result : bool) : bool :=
  match a with
  | [] => result
  | x :: xs => 
      if result 
      then all_equal_dec xs x
      else any_different_dec a x
  end.
(* !benchmark @end postcond_aux *)

Definition hasOnlyOneDistinctElement_postcond (a : (list Z)) (result : bool) (h_precond : hasOnlyOneDistinctElement_precond a) : Prop :=
  (* !benchmark @start postcond *)
  match a with
  | [] => result = true
  | x :: xs => (result = true -> all_equal xs x) /\ (result = false -> any_different a x)
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasOnlyOneDistinctElement_postcond_satisfied (a : (list Z)) (h_precond : hasOnlyOneDistinctElement_precond a) :
    hasOnlyOneDistinctElement_postcond a (hasOnlyOneDistinctElement a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
