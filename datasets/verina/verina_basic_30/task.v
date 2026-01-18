(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* empty *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint all_nonzero (b : list Z) : Prop :=
  match b with
  | [] => True
  | hd :: tl => hd <> 0%Z /\ all_nonzero tl
  end.

Fixpoint all_nonzero_dec (b : list Z) : bool :=
  match b with
  | [] => true
  | hd :: tl => (negb (Z.eqb hd 0%Z)) && all_nonzero_dec tl
  end.

Definition elementWiseModulo_precond_dec (a : list Z) (b : list Z) : bool :=
  (Nat.eqb (length a) (length b)) && (Nat.ltb 0 (length a)) && (all_nonzero_dec b).
(* !benchmark @end precond_aux *)

Definition elementWiseModulo_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  length a = length b /\ (length a > 0)%nat /\ all_nonzero b
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint map2_with_index (f : nat -> Z -> Z -> Z) (n : nat) (a : list Z) (b : list Z) : list Z :=
  match a, b with
  | [], [] => []
  | ha :: ta, hb :: tb => (f n ha hb) :: map2_with_index f (S n) ta tb
  | _, _ => []
  end.
(* !benchmark @end code_aux *)

Definition elementWiseModulo (a : (list Z)) (b : (list Z)) (h_precond : elementWiseModulo_precond a b) : (list Z) :=
  (* !benchmark @start code *)
  map2_with_index (fun i x y => Z.modulo x y) 0%nat a b
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  match l, n with
  | [], _ => default
  | hd :: _, 0%nat => hd
  | _ :: tl, S n' => nth_Z tl n' default
  end.

Fixpoint forall_indices (P : nat -> Prop) (n : nat) : Prop :=
  match n with
  | 0%nat => True
  | S n' => P n' /\ forall_indices P n'
  end.

Fixpoint forall_indices_dec (P : nat -> bool) (n : nat) : bool :=
  match n with
  | 0%nat => true
  | S n' => P n' && forall_indices_dec P n'
  end.

Definition elementWiseModulo_postcond_dec (a : list Z) (b : list Z) (result : list Z) : bool :=
  (Nat.eqb (length result) (length a)) &&
  (forall_indices_dec (fun i => Z.eqb (nth_Z result i 0%Z) (Z.modulo (nth_Z a i 0%Z) (nth_Z b i 0%Z))) (length result)).
(* !benchmark @end postcond_aux *)

Definition elementWiseModulo_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) (h_precond : elementWiseModulo_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  length result = length a /\ forall_indices (fun i => nth_Z result i 0%Z = Z.modulo (nth_Z a i 0%Z) (nth_Z b i 0%Z)) (length result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem elementWiseModulo_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : elementWiseModulo_precond a b) :
    elementWiseModulo_postcond a b (elementWiseModulo a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
