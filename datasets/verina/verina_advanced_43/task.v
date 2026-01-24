(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition maxStrength_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  negb (match nums with [] => true | _ => false end)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint powerSet_helper (l : list Z) (mask : nat) (idx : nat) : list Z :=
  match idx with
  | O => []
  | S idx' =>
    let rest := powerSet_helper l (Nat.div mask 2) idx' in
    if Nat.eqb (Nat.modulo mask 2) 1%nat then
      match nth_error l idx' with
      | Some v => v :: rest
      | None => rest
      end
    else rest
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition powerSet (l : list Z) : list (list Z) :=
  let n := length l in
  let masks := range (Nat.pow 2 n) in
  map (fun mask => powerSet_helper l mask n) masks.

Definition list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, _ => false
  end.

Definition productZ (l : list Z) : Z :=
  fold_left Z.mul l 1.

Fixpoint maxZ_list (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | [x] => x
  | x :: xs => Z.max x (maxZ_list xs default)
  end.
(* !benchmark @end code_aux *)

Definition maxStrength (nums : (list Z)) : Z :=
  (* !benchmark @start code *)
  let subsets := powerSet nums in
  let nonEmpty := filter (fun s => negb (list_Z_eqb s [])) subsets in
  let products := map productZ nonEmpty in
  maxZ_list products (-1000000)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    let rest := sublists xs in
    rest ++ map (fun s => x :: s) rest
  end.

Definition list_Z_eqb_full (l1 l2 : list Z) : bool :=
  (length l1 =? length l2)%nat &&
  forallb (fun p => (fst p =? snd p)) (combine l1 l2).

Definition list_Z_empty (l : list Z) : bool :=
  match l with [] => true | _ => false end.

Definition productZ_post (l : list Z) : Z :=
  fold_left Z.mul l 1.

Definition containsZ (l : list Z) (x : Z) : bool :=
  existsb (fun y => y =? x) l.
(* !benchmark @end postcond_aux *)

Definition maxStrength_postcond (nums : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let subs := sublists nums in
  let nonEmptySubs := filter (fun s => negb (list_Z_empty s)) subs in
  let products := map productZ_post nonEmptySubs in
  containsZ products result && forallb (fun p => p <=? result) products
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxStrength_postcond_satisfied (nums : (list Z)) :
    maxStrength_precond nums = true ->
    maxStrength_postcond nums (maxStrength nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
