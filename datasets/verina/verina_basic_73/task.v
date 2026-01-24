(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition Match_precond (s : string) (p : string) : bool :=
  (* !benchmark @start precond *)
  (length (list_ascii_of_string s) =? length (list_ascii_of_string p))%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint match_loop (sList pList : list ascii) : bool :=
  match sList, pList with
  | [], [] => true
  | sc :: sRest, pc :: pRest =>
    if negb (Ascii.eqb sc pc) && negb (Ascii.eqb pc "?"%char) then false
    else match_loop sRest pRest
  | _, _ => true
  end.
(* !benchmark @end code_aux *)

Definition Match (s : string) (p : string) : bool :=
  (* !benchmark @start code *)
  match_loop (list_ascii_of_string s) (list_ascii_of_string p)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_ascii (l : list ascii) (n : nat) : ascii :=
  match l with
  | [] => "000"%char
  | h :: t => match n with
              | O => h
              | S n' => nth_ascii t n'
              end
  end.

Fixpoint check_all_positions (sList pList : list ascii) (n len : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    let idx := (len - n)%nat in
    let sc := nth_ascii sList idx in
    let pc := nth_ascii pList idx in
    (Ascii.eqb sc pc || Ascii.eqb pc "?"%char) && check_all_positions sList pList n' len
  end.
(* !benchmark @end postcond_aux *)

Definition Match_postcond (s : string) (p : string) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let sList := list_ascii_of_string s in
  let pList := list_ascii_of_string p in
  let len := length sList in
  Bool.eqb result (check_all_positions sList pList len len)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem Match_postcond_satisfied (s : string) (p : string) :
    Match_precond s p = true ->
    Match_postcond s p (Match s p) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
