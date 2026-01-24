(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition removeElement_precond (lst : (list nat)) (target : nat) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint removeElement_helper (lst : list nat) (target : nat) : list nat :=
  match lst with
  | [] => []
  | x :: xs =>
    let rest := removeElement_helper xs target in
    if x =? target then rest else x :: rest
  end.
(* !benchmark @end code_aux *)

Definition removeElement (lst : (list nat)) (target : nat) : (list nat) :=
  (* !benchmark @start code *)
  removeElement_helper lst target
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Definition nth_opt {A : Type} (l : list A) (n : nat) : option A :=
  nth_error l n.

Fixpoint zipWithIndex_aux {A : Type} (l : list A) (idx : nat) : list (A * nat) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: zipWithIndex_aux xs (S idx)
  end.

Definition zipWithIndex {A : Type} (l : list A) : list (A * nat) :=
  zipWithIndex_aux l 0.

Definition check_indexed (lst' : list nat) (p : nat * nat) : bool :=
  let '(x, i) := p in
  match nth_error lst' i with
  | Some y => x =? y
  | None => false
  end.
(* !benchmark @end postcond_aux *)

Definition removeElement_postcond (lst : (list nat)) (target : nat) (result : (list nat)) : bool :=
  (* !benchmark @start postcond *)
  let lst' := filter (fun x => negb (x =? target)) lst in
  forallb (check_indexed lst') (zipWithIndex result) && (length result =? length lst')%nat
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem removeElement_postcond_satisfied (lst : (list nat)) (target : nat) :
    removeElement_precond lst target = true ->
    removeElement_postcond lst target (removeElement lst target) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
