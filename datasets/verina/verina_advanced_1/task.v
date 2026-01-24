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
Fixpoint count_Z (x : Z) (nums : list Z) : nat :=
  match nums with
  | [] => O
  | y :: ys => if (y =? x)%Z then S (count_Z x ys) else count_Z x ys
  end.

Fixpoint count_eq_nat (n : nat) (l : list nat) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? n)%nat then S (count_eq_nat n t) else count_eq_nat n t
  end.
(* !benchmark @end precond_aux *)

Definition FindSingleNumber_precond (nums : list Z) : bool :=
  (* !benchmark @start precond *)
  let numsCount := map (fun x => count_Z x nums) nums in
    forallb (fun c => orb (c =? 1)%nat (c =? 2)%nat) numsCount &&
    (count_eq_nat 1%nat numsCount =? 1)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint filterlist (x : Z) (nums : list Z) : list Z :=
  match nums with
  | [] => []
  | y :: ys => if (y =? x)%Z then y :: filterlist x ys else filterlist x ys
  end.

Fixpoint findUnique (remaining : list Z) (nums : list Z) : Z :=
  match remaining with
  | [] => 0
  | x :: xs =>
    let filtered := filterlist x nums in
    let cnt := length filtered in
    if (cnt =? 1)%nat then x else findUnique xs nums
  end.
(* !benchmark @end code_aux *)

Definition FindSingleNumber (nums : list Z) : Z :=
  (* !benchmark @start code *)
  findUnique nums nums
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint filterlist_post (x : Z) (nums : list Z) : list Z :=
  match nums with
  | [] => []
  | y :: ys => if (y =? x)%Z then y :: filterlist_post x ys else filterlist_post x ys
  end.

Fixpoint inb_Z (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else inb_Z x t
  end.
(* !benchmark @end postcond_aux *)

Definition FindSingleNumber_postcond (nums : list Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  (1 <=? length nums)%nat &&
    (length (filterlist_post result nums) =? 1)%nat &&
    forallb (fun x => implb (inb_Z x nums) (orb (x =? result)%Z (length (filterlist_post x nums) =? 2)%nat)) nums
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem FindSingleNumber_postcond_satisfied (nums : list Z) :
    FindSingleNumber_precond nums = true ->
    FindSingleNumber_postcond nums (FindSingleNumber nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
