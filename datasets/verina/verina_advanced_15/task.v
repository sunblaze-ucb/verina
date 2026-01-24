(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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

Definition increasingTriplet_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint lengthCheck (xs : list Z) (acc : nat) : nat :=
  match xs with
  | [] => acc
  | _ :: rest => lengthCheck rest (S acc)
  end.

Fixpoint loop (xs : list Z) (first : Z) (second : Z) : bool :=
  match xs with
  | [] => false
  | x :: rest =>
    if (x <=? first)%Z then
      loop rest x second
    else if (x <=? second)%Z then
      loop rest first x
    else
      true
  end.
(* !benchmark @end code_aux *)

Definition increasingTriplet (nums : (list Z)) : bool :=
  (* !benchmark @start code *)
  let len := lengthCheck nums O in
  if (len <? 3)%nat then
    false
  else
    match nums with
    | [] => false
    | f :: _ => loop nums f f
    end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition zipWithIndex {A : Type} (l : list A) : list (A * nat) :=
  let fix aux (l : list A) (idx : nat) : list (A * nat) :=
    match l with
    | [] => []
    | h :: t => (h, idx) :: aux t (S idx)
    end
  in aux l O.

Definition checkTriplet (nums' : list (Z * nat)) : bool :=
  existsb (fun xi =>
    existsb (fun yj =>
      existsb (fun zk =>
        let '(x, i) := xi in
        let '(y, j) := yj in
        let '(z, k) := zk in
        andb (andb (andb ((i <? j)%nat) ((j <? k)%nat)) ((x <? y)%Z)) ((y <? z)%Z)
      ) nums'
    ) nums'
  ) nums'.

Definition checkNoTriplet (nums' : list (Z * nat)) : bool :=
  forallb (fun xi =>
    forallb (fun yj =>
      forallb (fun zk =>
        let '(x, i) := xi in
        let '(y, j) := yj in
        let '(z, k) := zk in
        orb (orb (orb ((j <=? i)%nat) ((k <=? j)%nat)) ((y <=? x)%Z)) ((z <=? y)%Z)
      ) nums'
    ) nums'
  ) nums'.
(* !benchmark @end postcond_aux *)

Definition increasingTriplet_postcond (nums : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let nums' := zipWithIndex nums in
  andb (implb result (checkTriplet nums')) (implb (negb result) (checkNoTriplet nums'))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem increasingTriplet_postcond_satisfied (nums : (list Z)) :
    increasingTriplet_precond nums = true ->
    increasingTriplet_postcond nums (increasingTriplet nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
