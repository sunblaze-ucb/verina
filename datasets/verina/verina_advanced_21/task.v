(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition isPalindrome_precond_dec (s : string) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition isPalindrome_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_get {A : Type} (l : list A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | h :: _, 0 => Some h
  | _ :: t, S n' => list_get t n'
  end.

Fixpoint checkIndices_fuel (fuel left right : nat) (chars : list ascii) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
    if Nat.leb right left then
      true
    else
      match list_get chars left, list_get chars right with
      | Some cLeft, Some cRight =>
        if Ascii.eqb cLeft cRight then
          checkIndices_fuel fuel' (left + 1) (right - 1) chars
        else
          false
      | _, _ => false
      end
  end.

Fixpoint reverseList (acc : list ascii) (xs : list ascii) : list ascii :=
  match xs with
  | [] => acc
  | h :: t => reverseList (h :: acc) t
  end.

Fixpoint list_eqb_ascii (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => Ascii.eqb h1 h2 && list_eqb_ascii t1 t2
  | _, _ => false
  end.
(* !benchmark @end code_aux *)

Definition isPalindrome (s : string) (h_precond : isPalindrome_precond s) : bool :=
  (* !benchmark @start code *)
  let arr := list_ascii_of_string s in
  let length := length arr in
  if Nat.leb length 1%nat then
    true
  else
    let approach1 := checkIndices_fuel length 0 (length - 1) arr in
    let reversed := reverseList [] arr in
    let approach2 := list_eqb_ascii arr reversed in
    approach1 && approach2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isPalindrome_postcond_dec (s : string) (result : bool) : bool :=
  let arr := list_ascii_of_string s in
  let rev_arr := rev arr in
  if result then
    list_eqb_ascii arr rev_arr
  else
    negb (list_eqb_ascii arr rev_arr) && negb (Nat.eqb (length arr) 0).
(* !benchmark @end postcond_aux *)

Definition isPalindrome_postcond (s : string) (result : bool) (h_precond : isPalindrome_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (result = true -> list_ascii_of_string s = rev (list_ascii_of_string s)) /\
  (result = false -> (list_ascii_of_string s <> [] /\ list_ascii_of_string s <> rev (list_ascii_of_string s)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPalindrome_postcond_satisfied (s : string) (h_precond : isPalindrome_precond s) :
    isPalindrome_postcond s (isPalindrome s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
