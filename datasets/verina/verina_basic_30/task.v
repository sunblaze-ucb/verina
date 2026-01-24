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
Fixpoint forallb_indexed {A : Type} (f : nat -> A -> bool) (l : list A) (i : nat) : bool :=
  match l with
  | [] => true
  | h :: t => f i h && forallb_indexed f t (S i)
  end.
(* !benchmark @end precond_aux *)

Definition elementWiseModulo_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (length a =? length b)%nat && (1 <=? length a)%nat &&
    forallb_indexed (fun i x => negb (x =? 0)) b O
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint elementWiseModulo_aux (a : list Z) (b : list Z) : list Z :=
  match a, b with
  | [], _ => []
  | _, [] => []
  | ha :: ta, hb :: tb => (Z.rem ha hb) :: elementWiseModulo_aux ta tb
  end.
(* !benchmark @end code_aux *)

Definition elementWiseModulo (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  elementWiseModulo_aux a b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z (l : list Z) (n : nat) (d : Z) : Z :=
  match l, n with
  | [], _ => d
  | h :: _, O => h
  | _ :: t, S n' => nth_default_Z t n' d
  end.

Fixpoint check_all_indices (result a b : list Z) (i : nat) (len : nat) : bool :=
  match len with
  | O => true
  | S len' => 
      let ri := nth_default_Z result i 0 in
      let ai := nth_default_Z a i 0 in
      let bi := nth_default_Z b i 0 in
      (ri =? Z.rem ai bi) && check_all_indices result a b (S i) len'
  end.
(* !benchmark @end postcond_aux *)

Definition elementWiseModulo_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  (length result =? length a)%nat &&
    check_all_indices result a b O (length result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem elementWiseModulo_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    elementWiseModulo_precond a b = true ->
    elementWiseModulo_postcond a b (elementWiseModulo a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
