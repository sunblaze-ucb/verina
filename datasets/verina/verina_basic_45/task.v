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
Definition isEven_b (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Definition isOdd_b (n : Z) : bool :=
  negb (n mod 2 =? 0)%Z.
(* !benchmark @end precond_aux *)

Definition findProduct_precond (lst : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (2 <=? length lst)%nat && existsb isEven_b lst && existsb isOdd_b lst
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Definition isOdd (n : Z) : bool :=
  negb (n mod 2 =? 0)%Z.

Fixpoint findIdx_aux (lst : list Z) (pred : Z -> bool) (idx : nat) : option nat :=
  match lst with
  | [] => None
  | h :: t => if pred h then Some idx else findIdx_aux t pred (S idx)
  end.

Definition findIdx (lst : list Z) (pred : Z -> bool) : option nat :=
  findIdx_aux lst pred O.

Definition nth_default (lst : list Z) (n : nat) : Z :=
  nth n lst 0.

Definition firstEvenOddIndices (lst : list Z) : option (nat * nat) :=
  let evenIndex := findIdx lst isEven in
  let oddIndex := findIdx lst isOdd in
  match evenIndex, oddIndex with
  | Some ei, Some oi => Some (ei, oi)
  | _, _ => None
  end.
(* !benchmark @end code_aux *)

Definition findProduct (lst : (list Z)) : Z :=
  (* !benchmark @start code *)
  match firstEvenOddIndices lst with
  | Some (ei, oi) => (nth_default lst ei) * (nth_default lst oi)
  | None => 0
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isEven_post (n : Z) : bool :=
  (n mod 2 =? 0)%Z.

Definition isOdd_post (n : Z) : bool :=
  negb (n mod 2 =? 0)%Z.

Fixpoint findIdx_aux_post (lst : list Z) (pred : Z -> bool) (idx : nat) : option nat :=
  match lst with
  | [] => None
  | h :: t => if pred h then Some idx else findIdx_aux_post t pred (S idx)
  end.

Definition findIdx_post (lst : list Z) (pred : Z -> bool) : option nat :=
  findIdx_aux_post lst pred O.

Definition nth_default_post (lst : list Z) (n : nat) : Z :=
  nth n lst 0.

Definition firstEvenOddIndices_post (lst : list Z) : option (nat * nat) :=
  let evenIndex := findIdx_post lst isEven_post in
  let oddIndex := findIdx_post lst isOdd_post in
  match evenIndex, oddIndex with
  | Some ei, Some oi => Some (ei, oi)
  | _, _ => None
  end.
(* !benchmark @end postcond_aux *)

Definition findProduct_postcond (lst : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  match firstEvenOddIndices_post lst with
  | Some (ei, oi) => (result =? (nth_default_post lst ei) * (nth_default_post lst oi))%Z
  | None => true
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findProduct_postcond_satisfied (lst : (list Z)) :
    findProduct_precond lst = true ->
    findProduct_postcond lst (findProduct lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
