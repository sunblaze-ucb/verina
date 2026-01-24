(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Definition getLast_nat (l : list nat) (default : nat) : nat :=
  match l with
  | [] => default
  | _ => last l default
  end.
(* !benchmark @end precond_aux *)

Definition addTwoNumbers_precond (l1 : (list nat)) (l2 : (list nat)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length l1)%nat && (1 <=? length l2)%nat &&
  forallb (fun d => (d <? 10)%nat) l1 &&
  forallb (fun d => (d <? 10)%nat) l2 &&
  (negb (getLast_nat l1 0 =? 0)%nat || list_nat_eqb l1 [0]) &&
  (negb (getLast_nat l2 0 =? 0)%nat || list_nat_eqb l2 [0])
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint addAux (l1 l2 : list nat) (carry : nat) {struct l1} : list nat :=
  match l1 with
  | [] =>
    (* l1 is empty, process l2 with carry *)
    (fix addRest (l : list nat) (c : nat) : list nat :=
      match l with
      | [] => if (c =? 0)%nat then [] else [c]
      | h::t => let sum := (h + c)%nat in (sum mod 10)%nat :: addRest t (sum / 10)%nat
      end) l2 carry
  | h1::t1 =>
    match l2 with
    | [] =>
      let sum := (h1 + carry)%nat in
      (sum mod 10)%nat :: addAux t1 [] (sum / 10)%nat
    | h2::t2 =>
      let sum := (h1 + h2 + carry)%nat in
      (sum mod 10)%nat :: addAux t1 t2 (sum / 10)%nat
    end
  end.
(* !benchmark @end code_aux *)

Definition addTwoNumbers (l1 : (list nat)) (l2 : (list nat)) : (list nat) :=
  (* !benchmark @start code *)
  addAux l1 l2 0
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint listToNat (l : list nat) : nat :=
  match l with
  | [] => 0
  | d :: ds => (d + 10 * listToNat ds)%nat
  end.

Fixpoint list_nat_eqb_post (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb_post t1 t2
  | _, _ => false
  end.

Definition getLast_nat_post (l : list nat) (default : nat) : nat :=
  match l with
  | [] => default
  | _ => last l default
  end.
(* !benchmark @end postcond_aux *)

Definition addTwoNumbers_postcond (l1 : (list nat)) (l2 : (list nat)) (result : (list nat)) : bool :=
  (* !benchmark @start postcond *)
  (listToNat result =? listToNat l1 + listToNat l2)%nat &&
  forallb (fun d => (d <? 10)%nat) result &&
  (negb (getLast_nat_post result 0 =? 0)%nat || (list_nat_eqb_post l1 [0] && list_nat_eqb_post l2 [0] && list_nat_eqb_post result [0]))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem addTwoNumbers_postcond_satisfied (l1 : (list nat)) (l2 : (list nat)) :
    addTwoNumbers_precond l1 l2 = true ->
    addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
