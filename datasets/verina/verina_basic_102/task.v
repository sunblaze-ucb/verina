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
Fixpoint has_pair_with_sum (l : list Z) (target : Z) : bool :=
  match l with
  | [] => false
  | x :: xs => existsb (fun y => (x + y =? target)%Z) xs || has_pair_with_sum xs target
  end.
(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  (2 <=? length nums)%nat && has_pair_with_sum nums target
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, O => x
  | _ :: xs, S n' => nth_default_Z xs n'
  end.

Fixpoint inner_loop (nums : list Z) (target : Z) (i : nat) (j : nat) (n : nat) (fuel : nat) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
    if (j <? n)%nat then
      if (nth_default_Z nums i + nth_default_Z nums j =? target)%Z then
        Some j
      else
        inner_loop nums target i (S j) n fuel'
    else
      None
  end.

Fixpoint outer_loop (nums : list Z) (target : Z) (i : nat) (n : nat) (fuel : nat) : option (nat * nat) :=
  match fuel with
  | O => None
  | S fuel' =>
    if (S i <? n)%nat then
      match inner_loop nums target i (S i) n n with
      | Some j => Some (i, j)
      | None => outer_loop nums target (S i) n fuel'
      end
    else
      None
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) : (nat  * nat) :=
  (* !benchmark @start code *)
  let n := length nums in
  match outer_loop nums target 0 n n with
  | Some p => p
  | None => (O, O)
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z_post (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0%Z
  | x :: _, O => x
  | _ :: xs, S n' => nth_default_Z_post xs n'
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: xs => x :: take n' xs
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, l => l
  | _, [] => []
  | S n', _ :: xs => drop n' xs
  end.

Fixpoint zipIdx_aux {A : Type} (l : list A) (idx : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: zipIdx_aux xs (S idx)
  end.

Definition zipIdx {A : Type} (l : list A) : list (A * nat) := zipIdx_aux l 0.

Definition no_earlier_pair (nums : list Z) (i : nat) (target : Z) : bool :=
  forallb (fun p => let '(a, i') := p in
    forallb (fun b => negb (a + b =? target)%Z) (drop (S i') nums))
    (zipIdx (take i nums)).

Definition no_smaller_j (nums : list Z) (i j : nat) (target : Z) : bool :=
  forallb (fun b => negb (nth_default_Z_post nums i + b =? target)%Z)
    (take (j - i - 1) (drop (S i) nums)).
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (nat  * nat)) : bool :=
  (* !benchmark @start postcond *)
  let '(i, j) := result in
  (i <? j)%nat &&
  (j <? length nums)%nat &&
  (nth_default_Z_post nums i + nth_default_Z_post nums j =? target)%Z &&
  no_earlier_pair nums i target &&
  no_smaller_j nums i j target
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
