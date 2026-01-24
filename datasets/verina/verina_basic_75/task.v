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

Definition minArray_precond (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a : list Z) (i : nat) (currentMin : Z) : Z :=
  match i with
  | O => currentMin
  | S i' =>
    match a with
    | [] => currentMin
    | _ =>
      let idx := (length a - i)%nat in
      match nth_error a idx with
      | None => currentMin
      | Some v =>
        let newMin := if currentMin >? v then v else currentMin in
        loop a i' newMin
      end
    end
  end.

Definition minArray_helper (a : list Z) : Z :=
  match a with
  | [] => 0
  | h :: t => loop a (length t) h
  end.
(* !benchmark @end code_aux *)

Definition minArray (a : (list Z)) : Z :=
  (* !benchmark @start code *)
  minArray_helper a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forall_indices (a : list Z) (i : nat) (result : Z) : bool :=
  match i with
  | O => true
  | S i' =>
    match nth_error a i' with
    | None => forall_indices a i' result
    | Some v => (result <=? v) && forall_indices a i' result
    end
  end.
(* !benchmark @end postcond_aux *)

Definition minArray_postcond (a : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  forall_indices a (length a) result && existsb (fun x => x =? result) a
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem minArray_postcond_satisfied (a : (list Z)) :
    minArray_precond a = true ->
    minArray_postcond a (minArray a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
