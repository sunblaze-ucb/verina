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
Fixpoint list_sorted (nums : list Z) : bool :=
  match nums with
  | [] => true
  | [_] => true
  | h1 :: (h2 :: t) as tl => (h1 <=? h2) && list_sorted tl
  end.
(* !benchmark @end precond_aux *)

Definition removeDuplicates_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  list_sorted nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countUniques (prev : Z) (xs : list Z) (k : nat) : nat :=
  match xs with
  | [] => k
  | head :: tail =>
    if (head =? prev)%Z then
      countUniques prev tail k
    else
      countUniques head tail (k + 1)%nat
  end.
(* !benchmark @end code_aux *)

Definition removeDuplicates (nums : (list Z)) : nat :=
  (* !benchmark @start code *)
  match nums with
  | [] => O
  | h :: t => countUniques h t 1%nat
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint eraseDups (nums : list Z) : list Z :=
  match nums with
  | [] => []
  | h :: t =>
    let rest := eraseDups t in
    if existsb (fun x => x =? h) rest then rest else h :: rest
  end.
(* !benchmark @end postcond_aux *)

Definition removeDuplicates_postcond (nums : (list Z)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let dedupLen := length (eraseDups nums) in
  ((result - dedupLen)%nat =? O)%nat && (dedupLen <=? result)%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeDuplicates_postcond_satisfied (nums : (list Z)) :
    removeDuplicates_precond nums = true ->
    removeDuplicates_postcond nums (removeDuplicates nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
