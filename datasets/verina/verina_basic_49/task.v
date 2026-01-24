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

(* !benchmark @end precond_aux *)

Definition findFirstOdd_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isOdd (x : Z) : bool :=
  negb (x mod 2 =? 0).

Fixpoint findFirstOddHelper (l : list Z) (idx : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if isOdd x then Some idx else findFirstOddHelper xs (S idx)
  end.
(* !benchmark @end code_aux *)

Definition findFirstOdd (a : (list Z)) : (option nat) :=
  (* !benchmark @start code *)
  findFirstOddHelper a O
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isOdd_spec (x : Z) : bool :=
  negb (x mod 2 =? 0).

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint all_even_before (l : list Z) (idx : nat) : bool :=
  match idx with
  | O => true
  | S idx' => match l with
              | [] => true
              | x :: xs => negb (isOdd_spec x) && all_even_before xs idx'
              end
  end.

Fixpoint all_even (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (isOdd_spec x) && all_even xs
  end.
(* !benchmark @end postcond_aux *)

Definition findFirstOdd_postcond (a : (list Z)) (result : (option nat)) : bool :=
  (* !benchmark @start postcond *)
  match result with
  | Some idx => (idx <? length a)%nat && isOdd_spec (nth_Z a idx) && all_even_before a idx
  | None => all_even a
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstOdd_postcond_satisfied (a : (list Z)) :
    findFirstOdd_precond a = true ->
    findFirstOdd_postcond a (findFirstOdd a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
