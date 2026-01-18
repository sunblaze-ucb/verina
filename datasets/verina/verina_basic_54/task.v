(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import ZArith.
Require Import List.
Require Import Nat.
Require Import Bool.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* Helper: check if a list is pairwise sorted *)
Fixpoint is_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: y :: tl => (x <= y) /\ is_sorted (y :: tl)
  end.

Fixpoint is_sorted_dec (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: tl => (x <=? y) && is_sorted_dec (y :: tl)
  end.

Definition CanyonSearch_precond_dec (a : list Z) (b : list Z) : bool :=
  ((length a >? 0)%nat && (length b >? 0)%nat && is_sorted_dec a && is_sorted_dec b)%bool.
(* !benchmark @end precond_aux *)

Definition CanyonSearch_precond (a : (list Z)) (b : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  ((length a > 0)%nat /\ (length b > 0)%nat /\ is_sorted a /\ is_sorted b)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function for canyon search *)
Fixpoint canyonSearchAux (a b : list Z) (m n : nat) (d : nat) (fuel : nat) : nat :=
  match fuel with
  | O => d
  | S fuel' =>
    match nth_error a m, nth_error b n with
    | Some am, Some bn =>
      let diff := Z.abs_nat (am - bn) in
      let new_d := if (diff <? d)%nat then diff else d in
      if (am <=? bn)
      then canyonSearchAux a b (m + 1)%nat n new_d fuel'
      else canyonSearchAux a b m (n + 1)%nat new_d fuel'
    | _, _ => d
    end
  end.
(* !benchmark @end code_aux *)

Definition CanyonSearch (a : (list Z)) (b : (list Z)) (h_precond : CanyonSearch_precond a b) : nat :=
  (* !benchmark @start code *)
  match a, b with
| ah :: _, bh :: _ =>
  let init := Z.abs_nat (ah - bh) in
  canyonSearchAux a b 0%nat 0%nat init (length a + length b)%nat
| _, _ => 0%nat
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper: check if there exists a pair with the given difference *)
Fixpoint exists_pair_with_diff (a b : list Z) (d : nat) : Prop :=
  match a with
  | [] => False
  | ah :: atl =>
    (exists bh, In bh b /\ Z.abs_nat (ah - bh) = d) \/
    exists_pair_with_diff atl b d
  end.

(* Helper: check if all pairs have difference >= d *)
Fixpoint all_pairs_geq (a b : list Z) (d : nat) : Prop :=
  match a with
  | [] => True
  | ah :: atl =>
    (forall bh, In bh b -> (d <= Z.abs_nat (ah - bh))%nat) /\
    all_pairs_geq atl b d
  end.

Fixpoint exists_pair_with_diff_dec (a b : list Z) (d : nat) : bool :=
  match a with
  | [] => false
  | ah :: atl =>
    (existsb (fun bh => Nat.eqb (Z.abs_nat (ah - bh)) d) b) ||
    exists_pair_with_diff_dec atl b d
  end.

Fixpoint all_pairs_geq_dec (a b : list Z) (d : nat) : bool :=
  match a with
  | [] => true
  | ah :: atl =>
    (forallb (fun bh => (d <=? Z.abs_nat (ah - bh))%nat) b) &&
    all_pairs_geq_dec atl b d
  end.

Definition CanyonSearch_postcond_dec (a b : list Z) (result : nat) : bool :=
  (exists_pair_with_diff_dec a b result && all_pairs_geq_dec a b result)%bool.
(* !benchmark @end postcond_aux *)

Definition CanyonSearch_postcond (a : (list Z)) (b : (list Z)) (result : nat) (h_precond : CanyonSearch_precond a b) : Prop :=
  (* !benchmark @start postcond *)
  (exists_pair_with_diff a b result /\ all_pairs_geq a b result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem CanyonSearch_postcond_satisfied (a : (list Z)) (b : (list Z)) (h_precond : CanyonSearch_precond a b) :
    CanyonSearch_postcond a b (CanyonSearch a b h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
