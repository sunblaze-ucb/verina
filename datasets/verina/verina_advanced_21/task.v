(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
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

Definition isPalindrome_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (Ascii.eqb h1 h2) && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Fixpoint nth_ascii (n : nat) (l : list ascii) : option ascii :=
  match l with
  | [] => None
  | h :: t => match n with
              | O => Some h
              | S n' => nth_ascii n' t
              end
  end.

Fixpoint checkIndices (left right : nat) (chars : list ascii) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if (right <=? left)%nat then true
    else
      match nth_ascii left chars, nth_ascii right chars with
      | Some cLeft, Some cRight =>
        if Ascii.eqb cLeft cRight then
          checkIndices (left + 1)%nat (right - 1)%nat chars fuel'
        else false
      | _, _ => false
      end
  end.

Fixpoint reverseList (acc : list ascii) (xs : list ascii) : list ascii :=
  match xs with
  | [] => acc
  | h :: t => reverseList (h :: acc) t
  end.

Definition list_ascii_of_string (s : string) : list ascii :=
  let fix aux s :=
    match s with
    | EmptyString => []
    | String c rest => c :: aux rest
    end
  in aux s.
(* !benchmark @end code_aux *)

Definition isPalindrome (s : string) : bool :=
  (* !benchmark @start code *)
  let arr := list_ascii_of_string s in
  let len := length arr in
  if (len <=? 1)%nat then true
  else
    let approach1 := checkIndices 0%nat (len - 1)%nat arr len in
    let reversed := reverseList [] arr in
    let approach2 := list_ascii_eqb arr reversed in
    approach1 && approach2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_ascii_eqb_post (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (Ascii.eqb h1 h2) && list_ascii_eqb_post t1 t2
  | _, _ => false
  end.

Definition list_ascii_of_string_post (s : string) : list ascii :=
  let fix aux s :=
    match s with
    | EmptyString => []
    | String c rest => c :: aux rest
    end
  in aux s.
(* !benchmark @end postcond_aux *)

Definition isPalindrome_postcond (s : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let chars := list_ascii_of_string_post s in
  let revChars := rev chars in
  implb result (list_ascii_eqb_post chars revChars) &&
  implb (negb result) (negb (match chars with [] => true | _ => false end) && negb (list_ascii_eqb_post chars revChars))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem isPalindrome_postcond_satisfied (s : string) :
    isPalindrome_precond s = true ->
    isPalindrome_postcond s (isPalindrome s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
