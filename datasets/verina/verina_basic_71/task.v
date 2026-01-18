(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions needed *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions needed *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition LongestCommonPrefix_precond_dec (str1 : list ascii) (str2 : list ascii) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition LongestCommonPrefix_precond (str1 : (list ascii)) (str2 : (list ascii)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint LongestCommonPrefix_aux (str1 str2 : list ascii) (minLength : nat) (acc : list ascii) : list ascii :=
  match minLength with
  | 0 => acc
  | S minLength' =>
      match nth_error str1 (length acc), nth_error str2 (length acc) with
      | Some c1, Some c2 =>
          if ascii_dec c1 c2 then
            LongestCommonPrefix_aux str1 str2 minLength' (acc ++ [c1])
          else
            acc
      | _, _ => acc
      end
  end.
(* !benchmark @end code_aux *)

Definition LongestCommonPrefix (str1 : (list ascii)) (str2 : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) : (list ascii) :=
  (* !benchmark @start code *)
  let minLength := min (length str1) (length str2) in
LongestCommonPrefix_aux str1 str2 minLength []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint option_eq {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (o1 o2 : option A) : bool :=
  match o1, o2 with
  | Some x, Some y => if eq_dec x y then true else false
  | None, None => true
  | _, _ => false
  end.

Definition LongestCommonPrefix_postcond_dec (str1 str2 result : list ascii) : bool :=
  (length result <=? length str1) &&
  (if list_eq_dec ascii_dec result (firstn (length result) str1) then true else false) &&
  (length result <=? length str2) &&
  (if list_eq_dec ascii_dec result (firstn (length result) str2) then true else false) &&
  ((length result =? length str1) ||
   (length result =? length str2) ||
   negb (option_eq ascii_dec (nth_error str1 (length result)) (nth_error str2 (length result)))).
(* !benchmark @end postcond_aux *)

Definition LongestCommonPrefix_postcond (str1 : (list ascii)) (str2 : (list ascii)) (result : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) : Prop :=
  (* !benchmark @start postcond *)
  (length result <= length str1)%nat /\
result = firstn (length result) str1 /\
(length result <= length str2)%nat /\
result = firstn (length result) str2 /\
((length result = length str1)%nat \/
 (length result = length str2)%nat \/
 nth_error str1 (length result) <> nth_error str2 (length result))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestCommonPrefix_postcond_satisfied (str1 : (list ascii)) (str2 : (list ascii)) (h_precond : LongestCommonPrefix_precond str1 str2) :
    LongestCommonPrefix_postcond str1 str2 (LongestCommonPrefix str1 str2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
