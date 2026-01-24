(* !benchmark @start import type=task *)
Require Import String.
Require Import List.
Require Import Ascii.
Require Import Bool.
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

Definition longestCommonSubsequence_precond (s1 : string) (s2 : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint lcsAux (fuel : nat) (xs : list ascii) (ys : list ascii) : list ascii :=
  match fuel with
  | O => []
  | S fuel' =>
    match xs, ys with
    | [], _ => []
    | _, [] => []
    | x :: xs', y :: ys' =>
      if Ascii.eqb x y then
        x :: lcsAux fuel' xs' ys'
      else
        let left := lcsAux fuel' xs' (y :: ys') in
        let right := lcsAux fuel' (x :: xs') ys' in
        if (length right <=? length left)%nat then left else right
    end
  end.

Definition list_ascii_of_string (s : string) : list ascii :=
  list_ascii_of_string s.

Definition string_of_list_ascii (l : list ascii) : string :=
  string_of_list_ascii l.
(* !benchmark @end code_aux *)

Definition longestCommonSubsequence (s1 : string) (s2 : string) : string :=
  (* !benchmark @start code *)
  let xs := list_ascii_of_string s1 in
  let ys := list_ascii_of_string s2 in
  let fuel := (length xs + length ys + 1)%nat in
  let resultList := lcsAux fuel xs ys in
  string_of_list_ascii resultList
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allSubseq (arr : list ascii) : list (list ascii) :=
  match arr with
  | [] => [[]]
  | x :: xs =>
    let subs := allSubseq xs in
    subs ++ map (fun sub => x :: sub) subs
  end.

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => Ascii.eqb h1 h2 && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Definition list_contains (l : list (list ascii)) (x : list ascii) : bool :=
  existsb (fun y => list_ascii_eqb y x) l.
(* !benchmark @end postcond_aux *)

Definition longestCommonSubsequence_postcond (s1 : string) (s2 : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let chars1 := list_ascii_of_string s1 in
  let chars2 := list_ascii_of_string s2 in
  let resultChars := list_ascii_of_string result in
  let subseqA := allSubseq chars1 in
  let subseqB := allSubseq chars2 in
  let commonSubseq := filter (fun l => list_contains subseqB l) subseqA in
  list_contains commonSubseq resultChars && forallb (fun l => (length l <=? length resultChars)%nat) commonSubseq
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestCommonSubsequence_postcond_satisfied (s1 : string) (s2 : string) :
    longestCommonSubsequence_precond s1 s2 = true ->
    longestCommonSubsequence_postcond s1 s2 (longestCommonSubsequence s1 s2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
