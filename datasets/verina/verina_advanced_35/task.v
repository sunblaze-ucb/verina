(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
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
Fixpoint count_Z_code (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_Z_code x t) else count_Z_code x t
  end.

Fixpoint find_majority (candidates : list Z) (nums : list Z) : Z :=
  match candidates with
  | [] => 0
  | h :: t => if (length nums / 2 <? count_Z_code h nums)%nat then h else find_majority t nums
  end.
(* !benchmark @end code_aux *)

Definition majorityElement (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  find_majority nums nums
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
  forallb (fun x => implb (negb (x =? result)%Z) (count_Z_post x nums <=? n / 2)%nat) nums
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
