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
Fixpoint pairwise_le (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && pairwise_le tl
  end.
(* !benchmark @end precond_aux *)

Definition lastPosition_precond (arr : (list Z)) (elem : Z) : bool :=
  (* !benchmark @start precond *)
  pairwise_le arr
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (arr : list Z) (elem : Z) (i : nat) (pos : Z) : Z :=
  match arr with
  | [] => pos
  | a :: rest =>
    if a =? elem then loop rest elem (S i) (Z.of_nat i)
    else loop rest elem (S i) pos
  end.
(* !benchmark @end code_aux *)

Definition lastPosition (arr : (list Z)) (elem : Z) : Z :=
  (* !benchmark @start code *)
  loop arr elem O (-1)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n' default
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => l
  | S n', [] => []
  | S n', _ :: xs => drop n' xs
  end.
(* !benchmark @end postcond_aux *)

Definition lastPosition_postcond (arr : (list Z)) (elem : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  implb (result >=? 0)
        ((nth_Z arr (Z.to_nat result) 0 =? elem) &&
         forallb (fun x => negb (x =? elem)) (drop (Z.to_nat result + 1) arr))
  &&
  implb (result =? (-1))
        (forallb (fun x => negb (x =? elem)) arr)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem lastPosition_postcond_satisfied (arr : (list Z)) (elem : Z) :
    lastPosition_precond arr elem = true ->
    lastPosition_postcond arr elem (lastPosition arr elem) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
