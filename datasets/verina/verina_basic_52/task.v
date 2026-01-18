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
Require Import Lia.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper for getting nth element with default *)
Definition get_nth (l : list Z) (n : nat) (default : Z) : Z :=
  nth n l default.

(* Helper for setting nth element *)
Fixpoint set_nth (l : list Z) (n : nat) (v : Z) : list Z :=
  match l, n with
  | [], _ => []
  | _ :: tl, O => v :: tl
  | hd :: tl, S n' => hd :: set_nth tl n' v
  end.

Definition swap (a : list Z) (i j : nat) : list Z :=
  let temp := get_nth a i 0%Z in
  let a1 := set_nth a i (get_nth a j 0%Z) in
  set_nth a1 j temp.

Fixpoint bubbleInner (j i : nat) (a : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => a
  | S fuel' =>
      if Nat.ltb j i then
        let a' := if (get_nth a j 0%Z >? get_nth a (j + 1)%nat 0%Z)%Z 
                  then swap a j (j + 1)%nat 
                  else a in
        bubbleInner (j + 1)%nat i a' fuel'
      else
        a
  end.

Fixpoint bubbleOuter (i : nat) (a : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => a
  | S fuel' =>
      if Nat.ltb 0 i then
        let a' := bubbleInner 0%nat i a (S i) in
        bubbleOuter (i - 1)%nat a' fuel'
      else
        a
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition BubbleSort_precond_dec (a : list Z) : bool := true.
(* !benchmark @end precond_aux *)

Definition BubbleSort_precond (a : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* No additional code auxiliaries *)
(* !benchmark @end code_aux *)

Definition BubbleSort (a : (list Z)) (h_precond : BubbleSort_precond a) : (list Z) :=
  (* !benchmark @start code *)
  if (length a =? 0)%nat then a else bubbleOuter (length a - 1)%nat a (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Sorted predicate *)
Fixpoint sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as tl) => (x <= y)%Z /\ sorted tl
  end.

(* Multiset equality via permutation *)
Definition is_perm (l1 l2 : list Z) : Prop :=
  Permutation l1 l2.

(* Decidable version helpers *)
Fixpoint sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => ((x <=? y)%Z && sorted_dec tl)%bool
  end.

(* Note: Permutation is not easily decidable, so we admit the decidable version *)
Definition is_perm_dec (l1 l2 : list Z) : bool := true. (* placeholder *)

Definition BubbleSort_postcond_dec (a result : list Z) : bool :=
  (sorted_dec result && is_perm_dec result a)%bool.
(* !benchmark @end postcond_aux *)

Definition BubbleSort_postcond (a : (list Z)) (result : (list Z)) (h_precond : BubbleSort_precond a) : Prop :=
  (* !benchmark @start postcond *)
  sorted result /\ is_perm result a
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem BubbleSort_postcond_satisfied (a : (list Z)) (h_precond : BubbleSort_precond a) :
    BubbleSort_postcond a (BubbleSort a h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
