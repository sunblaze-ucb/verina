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

Definition ToArray_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)

(* !benchmark @end code_aux *)

Definition ToArray (xs : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  xs
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_Z (n : nat) (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_Z n' t default
              end
  end.

Fixpoint check_elements (i : nat) (arr : list Z) (xs : list Z) : bool :=
  match i with
  | O => true
  | S i' => let idx := (length xs - i)%nat in
            (nth_default_Z idx arr 0 =? nth_default_Z idx xs 0) && check_elements i' arr xs
  end.
(* !benchmark @end postcond_aux *)

Definition ToArray_postcond (xs : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length xs)%nat && check_elements (length xs) result xs)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem ToArray_postcond_satisfied (xs : (list Z)) :
    ToArray_precond xs = true ->
    ToArray_postcond xs (ToArray xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
