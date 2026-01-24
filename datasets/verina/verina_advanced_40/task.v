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

Definition maxOfList_precond (lst : (list nat)) : bool :=
  (* !benchmark @start precond *)
  negb (match lst with | [] => true | _ => false end)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint maxOfList_helper (lst : list nat) : nat :=
  match lst with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let maxTail := maxOfList_helper xs in
    if (maxTail <? x)%nat then x else maxTail
  end.
(* !benchmark @end code_aux *)

Definition maxOfList (lst : (list nat)) : nat :=
  (* !benchmark @start code *)
  maxOfList_helper lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint inList (x : nat) (lst : list nat) : bool :=
  match lst with
  | [] => false
  | h :: t => (h =? x)%nat || inList x t
  end.
(* !benchmark @end postcond_aux *)

Definition maxOfList_postcond (lst : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  inList result lst && forallb (fun x => (x <=? result)%nat) lst
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem maxOfList_postcond_satisfied (lst : (list nat)) :
    maxOfList_precond lst = true ->
    maxOfList_postcond lst (maxOfList lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
