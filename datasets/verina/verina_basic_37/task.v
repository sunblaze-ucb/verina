(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as tl) => (x <=? y) && is_sorted tl
  end.
(* !benchmark @end precond_aux *)

Definition findFirstOccurrence_precond (arr : (list Z)) (target : Z) : bool :=
  (* !benchmark @start precond *)
  is_sorted arr
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_default_Z xs n' default
  end.

Fixpoint loop (arr : list Z) (target : Z) (i : nat) (fuel : nat) : Z :=
  match fuel with
  | O => (-1)
  | S fuel' =>
    if (i <? length arr)%nat then
      let a := nth_default_Z arr i 0 in
      if (a =? target) then Z.of_nat i
      else if (a >? target) then (-1)
      else loop arr target (S i) fuel'
    else (-1)
  end.
(* !benchmark @end code_aux *)

Definition findFirstOccurrence (arr : (list Z)) (target : Z) : Z :=
  (* !benchmark @start code *)
  loop arr target O (length arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z_post (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | x :: _, O => x
  | _ :: xs, S n' => nth_default_Z_post xs n' default
  end.

Fixpoint forall_nat_lt (n : nat) (p : nat -> bool) : bool :=
  match n with
  | O => true
  | S n' => p n' && forall_nat_lt n' p
  end.
(* !benchmark @end postcond_aux *)

Definition findFirstOccurrence_postcond (arr : (list Z)) (target : Z) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  (implb (result >=? 0)
         ((nth_default_Z_post arr (Z.to_nat result) 0 =? target) &&
          forall_nat_lt (Z.to_nat result) (fun i => negb (nth_default_Z_post arr i 0 =? target))))
  &&
  (implb (result =? (-1))
         (forall_nat_lt (length arr) (fun i => negb (nth_default_Z_post arr i 0 =? target))))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstOccurrence_postcond_satisfied (arr : (list Z)) (target : Z) :
    findFirstOccurrence_precond arr target = true ->
    findFirstOccurrence_postcond arr target (findFirstOccurrence arr target) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
