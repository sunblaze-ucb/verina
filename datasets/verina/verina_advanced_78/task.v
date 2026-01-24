(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Nat.
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
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n' default
  end.

Definition pairwiseSum (nums : list Z) : list Z :=
  flat_map (fun i =>
    map (fun y => nth_Z nums i 0 + y) (skipn (S i) nums)
  ) (seq 0 (length nums)).

Fixpoint count_Z (l : list Z) (target : Z) : nat :=
  match l with
  | [] => O
  | x :: xs => if (x =? target)%Z then S (count_Z xs target) else count_Z xs target
  end.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  (1 <? length nums)%nat && (count_Z (pairwiseSum nums) target =? 1)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findComplement_aux (nums : list Z) (target : Z) (i : nat) (x : Z) (j : nat) : option nat :=
  match nums with
  | [] => None
  | y :: ys => if (x + y =? target)%Z then Some (i + j + 1)%nat else findComplement_aux ys target i x (j + 1)%nat
  end.

Definition findComplement (nums : list Z) (target : Z) (i : nat) (x : Z) : option nat :=
  findComplement_aux nums target i x 0.

Fixpoint twoSumAux (nums : list Z) (target : Z) (i : nat) : (nat * nat) :=
  match nums with
  | [] => (0%nat, 0%nat)
  | x :: xs =>
    match findComplement xs target i x with
    | Some j => (i, j)
    | None => twoSumAux xs target (i + 1)%nat
    end
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) : (nat * nat) :=
  (* !benchmark @start code *)
  twoSumAux nums target 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z_post (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z_post xs n' default
  end.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (nat * nat)) : bool :=
  (* !benchmark @start postcond *)
  let i := fst result in
  let j := snd result in
  (i <? j)%nat && (i <? length nums)%nat && (j <? length nums)%nat &&
  ((nth_Z_post nums i 0) + (nth_Z_post nums j 0) =? target)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) :
    twoSum_precond nums target = true ->
    twoSum_postcond nums target (twoSum nums target) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
