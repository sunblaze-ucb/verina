(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Require Import Ascii.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint ascii_eqb (a b : ascii) : bool :=
  match a, b with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7, Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3 &&
    Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition LongestCommonPrefix_precond (str1 : (list ascii)) (str2 : (list ascii)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint LongestCommonPrefix_aux (str1 str2 : list ascii) (idx : nat) (minLen : nat) (acc : list ascii) : list ascii :=
  match minLen with
  | O => acc
  | S minLen' =>
    match str1, str2 with
    | c1 :: str1', c2 :: str2' =>
      if ascii_eqb c1 c2 then
        LongestCommonPrefix_aux str1' str2' (S idx) minLen' (acc ++ [c1])
      else
        acc
    | _, _ => acc
    end
  end.
(* !benchmark @end code_aux *)

Definition LongestCommonPrefix (str1 : (list ascii)) (str2 : (list ascii)) : (list ascii) :=
  (* !benchmark @start code *)
  let minLength := Nat.min (length str1) (length str2) in
  LongestCommonPrefix_aux str1 str2 0 minLength []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => ascii_eqb h1 h2 && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Definition option_ascii_eqb (o1 o2 : option ascii) : bool :=
  match o1, o2 with
  | None, None => true
  | Some a1, Some a2 => ascii_eqb a1 a2
  | _, _ => false
  end.

Definition option_ascii_neqb (o1 o2 : option ascii) : bool :=
  negb (option_ascii_eqb o1 o2).
(* !benchmark @end postcond_aux *)

Definition LongestCommonPrefix_postcond (str1 : (list ascii)) (str2 : (list ascii)) (result : (list ascii)) : bool :=
  (* !benchmark @start postcond *)
  (length result <=? length str1)%nat &&
  list_ascii_eqb result (firstn (length result) str1) &&
  (length result <=? length str2)%nat &&
  list_ascii_eqb result (firstn (length result) str2) &&
  ((length result =? length str1)%nat ||
   (length result =? length str2)%nat ||
   option_ascii_neqb (nth_error str1 (length result)) (nth_error str2 (length result)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem LongestCommonPrefix_postcond_satisfied (str1 : (list ascii)) (str2 : (list ascii)) :
    LongestCommonPrefix_precond str1 str2 = true ->
    LongestCommonPrefix_postcond str1 str2 (LongestCommonPrefix str1 str2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
