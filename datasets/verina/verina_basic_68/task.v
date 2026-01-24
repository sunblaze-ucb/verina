(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition LinearSearch_precond (a : (list Z)) (e : Z) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint loop (a : list Z) (e : Z) (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if (n <? length a)%nat then
      match nth_error a n with
      | Some v => if (v =? e)%Z then n else loop a e (n + 1)%nat fuel'
      | None => n
      end
    else n
  end.
(* !benchmark @end code_aux *)

Definition LinearSearch (a : (list Z)) (e : Z) : nat :=
  (* !benchmark @start code *)
  loop a e 0%nat (length a)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint all_before_not_equal (a : list Z) (e : Z) (i : nat) : bool :=
  match i with
  | O => true
  | S i' =>
    match nth_error a i' with
    | Some v => negb (v =? e)%Z && all_before_not_equal a e i'
    | None => true
    end
  end.
(* !benchmark @end postcond_aux *)

Definition LinearSearch_postcond (a : (list Z)) (e : Z) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  (result <=? length a)%nat &&
  ((result =? length a)%nat ||
   match nth_error a result with
   | Some v => (v =? e)%Z
   | None => false
   end) &&
  all_before_not_equal a e result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LinearSearch_postcond_satisfied (a : (list Z)) (e : Z) :
    LinearSearch_precond a e = true ->
    LinearSearch_postcond a e (LinearSearch a e) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
