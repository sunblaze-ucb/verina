(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition SetToSeq_precond_dec (s : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition SetToSeq_precond (s : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint contains (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | (h :: t) => if (h =? x)%Z then true else contains t x
  end.

Fixpoint fold_left_dedup (l : list Z) (acc : list Z) : list Z :=
  match l with
  | [] => acc
  | (h :: t) => if contains acc h then fold_left_dedup t acc 
                else fold_left_dedup t (acc ++ [h])
  end.
(* !benchmark @end code_aux *)

Definition SetToSeq (s : (list Z)) (h_precond : SetToSeq_precond s) : (list Z) :=
  (* !benchmark @start code *)
  fold_left_dedup s []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all (l : list Z) (f : Z -> bool) : bool :=
  match l with
  | [] => true
  | (h :: t) => if f h then all t f else false
  end.

Fixpoint count (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | (h :: t) => if (h =? x)%Z then (1 + count t x)%nat else count t x
  end.

Fixpoint idxOf (l : list Z) (x : Z) (acc : nat) : nat :=
  match l with
  | [] => 0%nat
  | (h :: t) => if (h =? x)%Z then acc else idxOf t x (acc + 1)%nat
  end.

Fixpoint pairwise_ordered (l s result : list Z) : bool :=
  match l with
  | [] => true
  | (a :: rest) => 
      let check_a := fold_left (fun acc b =>
        andb acc (orb (negb (idxOf result a 0%nat <? idxOf result b 0%nat)%nat)
                      (idxOf s a 0%nat <? idxOf s b 0%nat)%nat)) rest true in
      andb check_a (pairwise_ordered rest s result)
  end.

Definition SetToSeq_postcond_dec (s result : list Z) : bool :=
  andb (andb (andb (all result (fun a => contains s a))
                   (all s (fun a => contains result a)))
             (all result (fun a => Nat.eqb (count result a) 1%nat)))
       (pairwise_ordered result s result).
(* !benchmark @end postcond_aux *)

Definition SetToSeq_postcond (s : (list Z)) (result : (list Z)) (h_precond : SetToSeq_precond s) : Prop :=
  (* !benchmark @start postcond *)
  all result (fun a => contains s a) = true /\
all s (fun a => contains result a) = true /\
all result (fun a => Nat.eqb (count result a) 1%nat) = true /\
pairwise_ordered result s result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SetToSeq_postcond_satisfied (s : (list Z)) (h_precond : SetToSeq_precond s) :
    SetToSeq_postcond s (SetToSeq s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
