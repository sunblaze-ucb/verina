(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition SetToSeq_precond (s : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_contains_Z (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else list_contains_Z t x
  end.

Definition foldl_unique (acc : list Z) (x : Z) : list Z :=
  if list_contains_Z acc x then acc else acc ++ [x].
(* !benchmark @end code_aux *)

Definition SetToSeq (s : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  fold_left foldl_unique s []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_Z t x) else count_Z t x
  end.

Fixpoint mem_Z (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else mem_Z x t
  end.

Fixpoint indexOf_Z (l : list Z) (x : Z) (idx : nat) : nat :=
  match l with
  | [] => idx
  | h :: t => if (h =? x)%Z then idx else indexOf_Z t x (S idx)
  end.

Definition idxOf_Z (l : list Z) (x : Z) : nat := indexOf_Z l x O.

Fixpoint pairwise_check (result s : list Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | a :: rest =>
    forallb (fun b => 
      implb ((idxOf_Z result a <? idxOf_Z result b)%nat)
            ((idxOf_Z s a <? idxOf_Z s b)%nat)) rest
    && pairwise_check result s rest
  end.
(* !benchmark @end postcond_aux *)

Definition SetToSeq_postcond (s : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  forallb (fun a => mem_Z a s) result &&
  forallb (fun a => mem_Z a result) s &&
  forallb (fun a => (count_Z result a =? 1)%nat) result &&
  pairwise_check result s result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem SetToSeq_postcond_satisfied (s : (list Z)) :
    SetToSeq_precond s = true ->
    SetToSeq_postcond s (SetToSeq s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
