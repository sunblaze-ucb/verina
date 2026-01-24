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

Definition CountLessThan_precond (numbers : (list Z)) (threshold : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countLessThanHelper (numbers : list Z) (threshold : Z) : nat :=
  match numbers with
  | [] => O
  | h :: t => if (h <? threshold)%Z 
              then S (countLessThanHelper t threshold)
              else countLessThanHelper t threshold
  end.
(* !benchmark @end code_aux *)

Definition CountLessThan (numbers : (list Z)) (threshold : Z) : nat :=
  (* !benchmark @start code *)
  countLessThanHelper numbers threshold
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint foldCountLessThan (numbers : list Z) (threshold : Z) (acc : nat) : nat :=
  match numbers with
  | [] => acc
  | h :: t => if (h <? threshold)%Z 
              then foldCountLessThan t threshold (S acc)
              else foldCountLessThan t threshold acc
  end.
(* !benchmark @end postcond_aux *)

Definition CountLessThan_postcond (numbers : (list Z)) (threshold : Z) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let expected := foldCountLessThan numbers threshold O in
  ((result - expected =? 0)%nat && (expected - result =? 0)%nat)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CountLessThan_postcond_satisfied (numbers : (list Z)) (threshold : Z) :
    CountLessThan_precond numbers threshold = true ->
    CountLessThan_postcond numbers threshold (CountLessThan numbers threshold) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
