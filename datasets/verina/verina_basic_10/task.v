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

Definition isGreater_precond (n : Z) (a : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length a)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition isGreater (n : Z) (a : (list Z)) : bool :=
  (* !benchmark @start code *)
  forallb (fun x => n >? x) a
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_indices_check (n : Z) (a : list Z) (i : nat) : bool :=
  match a with
  | [] => true
  | h :: t => (n >? h) && all_indices_check n t (S i)
  end.
(* !benchmark @end postcond_aux *)

Definition isGreater_postcond (n : Z) (a : (list Z)) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  Bool.eqb (all_indices_check n a O) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isGreater_postcond_satisfied (n : Z) (a : (list Z)) :
    isGreater_precond n a = true ->
    isGreater_postcond n a (isGreater n a) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
