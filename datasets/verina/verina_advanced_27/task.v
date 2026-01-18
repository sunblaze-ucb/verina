(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition longestCommonSubsequence_precond_dec (s1 : string) (s2 : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition longestCommonSubsequence_precond (s1 : string) (s2 : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: list_of_string rest
  end.

Fixpoint string_of_list (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (string_of_list rest)
  end.

Fixpoint lcsAux (xs : list ascii) (ys : list ascii) : list ascii :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
      if ascii_dec x y then
        x :: lcsAux xs' ys'
      else
        let left := lcsAux xs' (y :: ys') in
        let right := lcsAux (x :: xs') ys' in
        if (length left >=? length right)%nat then left else right
  end.
(* !benchmark @end code_aux *)

Definition longestCommonSubsequence (s1 : string) (s2 : string) (h_precond : longestCommonSubsequence_precond s1 s2) : string :=
  (* !benchmark @start code *)
  let xs := list_of_string s1 in
  let ys := list_of_string s2 in
  let resultList := lcsAux xs ys in
  string_of_list resultList
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint allSubseq_aux (arr : list ascii) : list (list ascii) :=
  match arr with
  | [] => [[]]
  | x :: xs =>
      let rest := allSubseq_aux xs in
      rest ++ map (fun sub => x :: sub) rest
  end.

Definition allSubseq (arr : list ascii) : list (list ascii) :=
  map (@rev ascii) (allSubseq_aux arr).

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => if ascii_dec x y then list_ascii_eqb xs ys else false
  | _, _ => false
  end.

Fixpoint list_contains (l : list ascii) (ll : list (list ascii)) : bool :=
  match ll with
  | [] => false
  | x :: xs => if list_ascii_eqb l x then true else list_contains l xs
  end.

Fixpoint list_all (f : list ascii -> bool) (ll : list (list ascii)) : bool :=
  match ll with
  | [] => true
  | x :: xs => if f x then list_all f xs else false
  end.

Definition longestCommonSubsequence_postcond_dec (s1 : string) (s2 : string) (result : string) : bool :=
  let subseqA := allSubseq (list_of_string s1) in
  let subseqB := allSubseq (list_of_string s2) in
  let commonSubseq := filter (fun l => list_contains l subseqB) subseqA in
  andb (list_contains (list_of_string result) commonSubseq)
       (list_all (fun l => (length l <=? length (list_of_string result))%nat) commonSubseq).
(* !benchmark @end postcond_aux *)

Definition longestCommonSubsequence_postcond (s1 : string) (s2 : string) (result : string) (h_precond : longestCommonSubsequence_precond s1 s2) : Prop :=
  (* !benchmark @start postcond *)
  let subseqA := allSubseq (list_of_string s1) in
  let subseqB := allSubseq (list_of_string s2) in
  let commonSubseq := filter (fun l => list_contains l subseqB) subseqA in
  In (list_of_string result) commonSubseq /\ Forall (fun l => (length l <= length (list_of_string result))%nat) commonSubseq
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem longestCommonSubsequence_postcond_satisfied (s1 : string) (s2 : string) (h_precond : longestCommonSubsequence_precond s1 s2) :
    longestCommonSubsequence_postcond s1 s2 (longestCommonSubsequence s1 s2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
