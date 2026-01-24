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
Definition isEven (n : Z) : bool := (n mod 2 =? 0)%Z.
Definition isOdd (n : Z) : bool := negb (n mod 2 =? 0)%Z.
(* !benchmark @end precond_aux *)

Definition firstEvenOddDifference_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (Z.of_nat (length a) >? 1)%Z && existsb (fun x => isEven x) a && existsb (fun x => isOdd x) a
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isEvenCode (n : Z) : bool := (n mod 2 =? 0)%Z.
Definition isOddCode (n : Z) : bool := negb (n mod 2 =? 0)%Z.

Fixpoint findFirstEvenOdd (lst : list Z) (i : nat) (firstEven firstOdd : option nat) (orig : list Z) : Z :=
  match lst with
  | [] => 0%Z
  | x :: rest =>
    let newFirstEven := match firstEven with
                        | None => if isEvenCode x then Some i else None
                        | Some _ => firstEven
                        end in
    let newFirstOdd := match firstOdd with
                       | None => if isOddCode x then Some i else None
                       | Some _ => firstOdd
                       end in
    match newFirstEven, newFirstOdd with
    | Some e, Some o => (nth e orig 0%Z) - (nth o orig 0%Z)
    | _, _ => findFirstEvenOdd rest (S i) newFirstEven newFirstOdd orig
    end
  end.
(* !benchmark @end code_aux *)

Definition firstEvenOddDifference (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  findFirstEvenOdd a O None None a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isEvenPost (n : Z) : bool := (n mod 2 =? 0)%Z.
Definition isOddPost (n : Z) : bool := negb (n mod 2 =? 0)%Z.

Fixpoint allOddBefore (a : list Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' => match a with
            | [] => true
            | x :: rest => if (i' <? length rest)%nat 
                           then isOddPost (nth i' a 0%Z) && allOddBefore a i'
                           else allOddBefore a i'
            end
  end.

Fixpoint allEvenBefore (a : list Z) (j : nat) : bool :=
  match j with
  | O => true
  | S j' => match a with
            | [] => true
            | x :: rest => if (j' <? length rest)%nat
                           then isEvenPost (nth j' a 0%Z) && allEvenBefore a j'
                           else allEvenBefore a j'
            end
  end.

Fixpoint checkAllOddBefore (a : list Z) (i : nat) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => isOddPost (nth k' a 0%Z) && checkAllOddBefore a i k'
  end.

Fixpoint checkAllEvenBefore (a : list Z) (j : nat) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => isEvenPost (nth k' a 0%Z) && checkAllEvenBefore a j k'
  end.

Fixpoint existsIJ (a : list Z) (result : Z) (i : nat) : bool :=
  match i with
  | O => false
  | S i' =>
    let checkI := (i' <? length a)%nat && isEvenPost (nth i' a 0%Z) in
    if checkI then
      (fix checkJ (j : nat) : bool :=
        match j with
        | O => false
        | S j' =>
          let checkJCond := (j' <? length a)%nat && isOddPost (nth j' a 0%Z) in
          if checkJCond then
            if (result =? (nth i' a 0%Z) - (nth j' a 0%Z))%Z &&
               checkAllOddBefore a i' i' && checkAllEvenBefore a j' j'
            then true
            else checkJ j'
          else checkJ j'
        end) (length a)
      || existsIJ a result i'
    else existsIJ a result i'
  end.
(* !benchmark @end postcond_aux *)

Definition firstEvenOddDifference_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  existsIJ a result (length a)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem firstEvenOddDifference_postcond_satisfied (a : (list Z)) :
    firstEvenOddDifference_precond a = true ->
    firstEvenOddDifference_postcond a (firstEvenOddDifference a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
