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

Definition below_zero_precond (operations : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint buildS_aux (operations : list Z) (acc : Z) : list Z :=
  match operations with
  | [] => []
  | op :: ops => let new_acc := acc + op in new_acc :: buildS_aux ops new_acc
  end.

Definition buildS (operations : list Z) : list Z :=
  0 :: buildS_aux operations 0.

Fixpoint check_negative (lst : list Z) : bool :=
  match lst with
  | [] => false
  | x :: xs => if (x <? 0)%Z then true else check_negative xs
  end.
(* !benchmark @end code_aux *)

Definition below_zero (operations : (list Z)) : (list Z * bool) :=
  (* !benchmark @start code *)
  let s := buildS operations in
  let result := check_negative (tl s) in
  (s, result)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint nth_Z_opt (l : list Z) (n : nat) : option Z :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: xs, S n' => nth_Z_opt xs n'
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition option_Z_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => (x =? y)%Z
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition below_zero_postcond (operations : (list Z)) (result : (list Z * bool)) : bool :=
  (* !benchmark @start postcond *)
  let s := fst result in
  let res := snd result in
  let len_s := length s in
  let len_ops := length operations in
  (len_s =? len_ops + 1)%nat &&
  option_Z_eqb (nth_Z_opt s 0) (Some 0) &&
  forallb (fun i => option_Z_eqb (nth_Z_opt s (i + 1)%nat) (Some (nth_Z s i + nth (i)%nat operations 0))) (range len_ops) &&
  implb res (existsb (fun i => (nth_Z s (i + 1)%nat <? 0)%Z) (range len_ops)) &&
  implb (negb res) (forallb (fun x => (x >=? 0)%Z) s)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem below_zero_postcond_satisfied (operations : (list Z)) :
    below_zero_precond operations = true ->
    below_zero_postcond operations (below_zero operations) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
