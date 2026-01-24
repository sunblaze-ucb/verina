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

Definition maxSubarraySum_precond (numbers : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint isAllNegative (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => if (x >=? 0)%Z then false else isAllNegative xs
  end.

Fixpoint findMaxProduct (l : list Z) (currMax : Z) (currSum : Z) : Z :=
  match l with
  | [] => currMax
  | [x] => Z.max currMax x
  | x :: ((y :: rest) as tail) =>
      let newSum := Z.max y (currSum + y) in
      let newMax := Z.max currMax newSum in
      findMaxProduct tail newMax newSum
  end.

Definition handleList (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest =>
      if isAllNegative xs then 0
      else
        let initialMax := Z.max 0 x in
        let startSum := Z.max 0 x in
        findMaxProduct xs initialMax startSum
  end.
(* !benchmark @end code_aux *)

Definition maxSubarraySum (numbers : (list Z)) : Z :=
  (* !benchmark @start code *)
  handleList numbers
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sumZ (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sumZ xs
  end.

Fixpoint take_Z (n : nat) (l : list Z) : list Z :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: take_Z n' xs
            end
  end.

Fixpoint drop_Z (n : nat) (l : list Z) : list Z :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | x :: xs => drop_Z n' xs
            end
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition subArraySums (numbers : list Z) : list Z :=
  let len := length numbers in
  flat_map (fun start =>
    map (fun l =>
      sumZ (take_Z l (drop_Z start numbers)))
      (range (len - start + 1)%nat))
    (range (len + 1)%nat).

Definition containsZ (l : list Z) (v : Z) : bool :=
  existsb (fun x => (x =? v)%Z) l.

Definition allLeZ (l : list Z) (v : Z) : bool :=
  forallb (fun x => (x <=? v)%Z) l.
(* !benchmark @end postcond_aux *)

Definition maxSubarraySum_postcond (numbers : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let sums := subArraySums numbers in
  containsZ sums result && allLeZ sums result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxSubarraySum_postcond_satisfied (numbers : (list Z)) :
    maxSubarraySum_precond numbers = true ->
    maxSubarraySum_postcond numbers (maxSubarraySum numbers) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
