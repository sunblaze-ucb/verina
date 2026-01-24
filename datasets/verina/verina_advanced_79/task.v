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

(* !benchmark @end precond_aux *)

Definition twoSum_precond (nums : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint inner (x : Z) (target : Z) (lst' : list Z) (j : nat) : option nat :=
  match lst' with
  | [] => None
  | y :: ys =>
    if (x + y =? target)%Z then Some j
    else inner x target ys (j + 1)%nat
  end.

Fixpoint outer (nums : list Z) (target : Z) (lst : list Z) (i : nat) : option (nat * nat) :=
  match lst with
  | [] => None
  | x :: xs =>
    match inner x target xs (i + 1)%nat with
    | Some j => Some (i, j)
    | None => outer nums target xs (i + 1)%nat
    end
  end.
(* !benchmark @end code_aux *)

Definition twoSum (nums : (list Z)) (target : Z) : (option (nat  * nat)) :=
  (* !benchmark @start code *)
  outer nums target nums 0%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z (l : list Z) (n : nat) (d : Z) : Z :=
  match l with
  | [] => d
  | x :: xs => match n with
               | O => x
               | S n' => nth_default_Z xs n' d
               end
  end.

Definition nth_Z (l : list Z) (n : nat) : Z := nth_default_Z l n 0.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: take n' xs
            end
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | _ :: xs => drop n' xs
            end
  end.

Fixpoint zipIdx_aux {A : Type} (l : list A) (start : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, start) :: zipIdx_aux xs (start + 1)%nat
  end.

Definition zipIdx {A : Type} (l : list A) : list (A * nat) := zipIdx_aux l 0%nat.

Definition pairwise_sum_neq (target : Z) (nums : list Z) : bool :=
  forallb (fun p => 
    let '(a, i') := p in
    forallb (fun b => negb (a + b =? target)%Z) (drop (i' + 1)%nat nums)
  ) (zipIdx nums).

Definition check_lexico_first (nums : list Z) (target : Z) (i : nat) : bool :=
  forallb (fun p =>
    let '(a, i') := p in
    forallb (fun b => negb (a + b =? target)%Z) (drop (i' + 1)%nat nums)
  ) (zipIdx (take i nums)).

Definition check_smallest_j (nums : list Z) (i j : nat) (target : Z) : bool :=
  forallb (fun b => negb (nth_Z nums i + b =? target)%Z) 
          (take (j - i - 1)%nat (drop (i + 1)%nat nums)).
(* !benchmark @end postcond_aux *)

Definition twoSum_postcond (nums : (list Z)) (target : Z) (result : (option (nat  * nat))) : bool :=
  (* !benchmark @start postcond *)
  match result with
  | None => pairwise_sum_neq target nums
  | Some (i, j) =>
    (i <? j)%nat &&
    (j <? length nums)%nat &&
    (nth_Z nums i + nth_Z nums j =? target)%Z &&
    check_lexico_first nums target i &&
    check_smallest_j nums i j target
  end
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
