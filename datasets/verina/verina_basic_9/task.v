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

Definition hasCommonElement_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat && (1 <=? length b)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition hasCommonElement (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start code *)
  existsb (fun x => existsb (fun y => x =? y) b) a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint hasCommonElement_check (a b : list Z) : bool :=
  match a with
  | [] => false
  | x :: xs => existsb (fun y => x =? y) b || hasCommonElement_check xs b
  end.
(* !benchmark @end postcond_aux *)

Definition hasCommonElement_postcond (a : (list Z)) (b : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (hasCommonElement_check a b) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasCommonElement_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    hasCommonElement_precond a b = true ->
    hasCommonElement_postcond a b (hasCommonElement a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
