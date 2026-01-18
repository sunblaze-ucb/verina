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
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* empty *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint flatMap {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x ++ flatMap f xs
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => l
  | S n', [] => []
  | S n', _ :: xs => drop n' xs
  end.

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint count_Z (target : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | x :: xs => if (x =? target)%Z then S (count_Z target xs) else count_Z target xs
  end.

Definition pairwiseSum (nums : list Z) : list Z :=
  flatMap (fun i =>
    map (fun y => (nth_Z nums i + y)%Z) (drop (i + 1)%nat nums))
  (range (length nums)).

Definition twoSum_precond_dec (nums : list Z) (target : Z) : bool :=
  ((length nums >? 1)%nat && Nat.eqb (count_Z target (pairwiseSum nums)) 1%nat)%bool.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : Prop :=
  (* !benchmark @start precond *)
  let pairwiseSum := flatMap (fun i =>
    map (fun y => (nth_Z nums i + y)%Z) (drop (i + 1)%nat nums))
  (range (length nums)) in
  ((length nums) > 1%nat)%nat /\ count_Z target pairwiseSum = 1%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findComplement_aux (nums : list Z) (target : Z) (x : Z) (j : nat) : option nat :=
  match nums with
  | [] => None
  | y :: ys => if ((x + y) =? target)%Z then Some j else findComplement_aux ys target x (j + 1)%nat
  end.

Definition findComplement (nums : list Z) (target : Z) (i : nat) (x : Z) : option nat :=
  match findComplement_aux nums target x 0%nat with
  | Some j => Some (i + j + 1)%nat
  | None => None
  end.

Fixpoint twoSumAux (nums : list Z) (target : Z) (i : nat) (fuel : nat) : nat * nat :=
  match fuel with
  | O => (0%nat, 0%nat)
  | S fuel' =>
    match nums with
    | [] => (0%nat, 0%nat)
    | x :: xs =>
      match findComplement xs target i x with
      | Some j => (i, j)
      | None => twoSumAux xs target (i + 1)%nat fuel'
      end
    end
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) : (nat * nat) :=
  (* !benchmark @start code *)
  twoSumAux nums target 0%nat (length nums)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition twoSum_postcond_dec (nums : list Z) (target : Z) (result : nat * nat) : bool :=
  let i := fst result in
  let j := snd result in
  ((i <? j)%nat && (i <? length nums)%nat && (j <? length nums)%nat && 
   ((nth_Z nums i + nth_Z nums j) =? target)%Z)%bool.
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (nat * nat)) (h_precond : twoSum_precond nums target) : Prop :=
  (* !benchmark @start postcond *)
  let i := fst result in
  let j := snd result in
  (i < j)%nat /\
  (i < length nums)%nat /\ (j < length nums)%nat /\
  (nth_Z nums i + nth_Z nums j)%Z = target
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem twoSum_postcond_satisfied (nums : (list Z)) (target : Z) (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
