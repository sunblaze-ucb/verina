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
Fixpoint count_Z (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_Z x t) else count_Z x t
  end.
(* !benchmark @end precond_aux *)

Definition majorityElement_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length nums)%nat && existsb (fun x => (length nums / 2 <? count_Z x nums)%nat) nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint insert_Z (x : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => [x]
  | h :: t =>
    if (x <=? h)%Z then x :: h :: t
    else h :: insert_Z x t
  end.

Fixpoint insertionSort_Z (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | h :: t => insert_Z h (insertionSort_Z t)
  end.

Definition getAt_Z (xs : list Z) (i : nat) : Z :=
  match skipn i xs with
  | [] => 0
  | h :: _ => h
  end.
(* !benchmark @end code_aux *)

Definition majorityElement (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  let sorted := insertionSort_Z nums in
  let len := length sorted in
  let mid := (len / 2)%nat in
  getAt_Z sorted mid
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_Z_post (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_Z_post x t) else count_Z_post x t
  end.
(* !benchmark @end postcond_aux *)

Definition majorityElement_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let n := length nums in
  (n / 2 <? count_Z_post result nums)%nat &&
  forallb (fun x => orb (x =? result)%Z ((count_Z_post x nums <=? n / 2)%nat)) nums
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem majorityElement_postcond_satisfied (nums : (list Z)) :
    majorityElement_precond nums = true ->
    majorityElement_postcond nums (majorityElement nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
