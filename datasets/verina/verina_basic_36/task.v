(* !benchmark @start import type=task *)
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition isSpaceCommaDot (c : ascii) : bool :=
  if (c =? " ")%char then true
  else if (c =? ",")%char then true
  else if (c =? ".")%char then true
  else false.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition replaceWithColon_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition replaceCharWithColon (c : ascii) : ascii :=
  if isSpaceCommaDot c then ":"
  else c.

Fixpoint mapChars (cs : list ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: rest => replaceCharWithColon c :: mapChars rest
  end.
(* !benchmark @end code_aux *)

Definition replaceWithColon (s : string) : string :=
  (* !benchmark @start code *)
  let cs := list_ascii_of_string s in
  let cs' := mapChars cs in
  string_of_list_ascii cs'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%char && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Fixpoint nth_ascii (n : nat) (l : list ascii) (default : ascii) : ascii :=
  match n, l with
  | O, x :: _ => x
  | S n', _ :: t => nth_ascii n' t default
  | _, [] => default
  end.

Fixpoint checkAllIndices (i : nat) (len : nat) (cs cs' : list ascii) : bool :=
  match i with
  | O => 
    if (O <? len)%nat then
      let c := nth_ascii O cs "000"%char in
      let c' := nth_ascii O cs' "000"%char in
      implb (isSpaceCommaDot c) (c' =? ":")%char &&
      implb (negb (isSpaceCommaDot c)) (c' =? c)%char
    else true
  | S i' =>
    (if (i <? len)%nat then
      let c := nth_ascii i cs "000"%char in
      let c' := nth_ascii i cs' "000"%char in
      implb (isSpaceCommaDot c) (c' =? ":")%char &&
      implb (negb (isSpaceCommaDot c)) (c' =? c)%char
    else true) && checkAllIndices i' len cs cs'
  end.
(* !benchmark @end postcond_aux *)

Definition replaceWithColon_postcond (s : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string s in
  let cs' := list_ascii_of_string result in
  let len := length cs in
  (length cs' =? len)%nat && checkAllIndices (len - 1) len cs cs'
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem replaceWithColon_postcond_satisfied (s : string) :
    replaceWithColon_precond s = true ->
    replaceWithColon_postcond s (replaceWithColon s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
