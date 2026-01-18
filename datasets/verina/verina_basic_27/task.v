(* !benchmark @start import type=task *)
Require Import Ascii.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Sets.Ensembles.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper to convert string to list of ascii *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_list s'
  end.

(* Check if element is in list *)
Fixpoint mem_ascii (c : ascii) (l : list ascii) : bool :=
  match l with
  | nil => false
  | h :: t => if ascii_dec c h then true else mem_ascii c t
  end.

(* Main loop helper *)
Fixpoint findFirstRepeatedChar_loop (cs : list ascii) (i : nat) (seen : list ascii) : option ascii :=
  match cs with
  | nil => None
  | c :: cs' =>
      if i =? 0 then
        if mem_ascii c seen then Some c
        else findFirstRepeatedChar_loop cs' 0 (c :: seen)
      else
        findFirstRepeatedChar_loop cs' (i - 1)%nat seen
  end.

Fixpoint findFirstRepeatedChar_aux (cs : list ascii) (seen : list ascii) : option ascii :=
  match cs with
  | nil => None
  | c :: cs' =>
      if mem_ascii c seen then Some c
      else findFirstRepeatedChar_aux cs' (c :: seen)
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition findFirstRepeatedChar_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition findFirstRepeatedChar_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to count occurrences of a character *)
Fixpoint count_char (c : ascii) (l : list ascii) : nat :=
  match l with
  | nil => 0%nat
  | h :: t => if ascii_dec c h then S (count_char c t) else count_char c t
  end.

(* Helper to find index of first occurrence *)
Fixpoint indexOf_char (c : ascii) (l : list ascii) : nat :=
  match l with
  | nil => 0%nat
  | h :: t => if ascii_dec c h then 0%nat else S (indexOf_char c t)
  end.
(* !benchmark @end code_aux *)

Definition findFirstRepeatedChar (s : string) (h_precond : findFirstRepeatedChar_precond s) : (option ascii) :=
  (* !benchmark @start code *)
  findFirstRepeatedChar_aux (string_to_list s) []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Check if all elements in a list are pairwise different *)
Fixpoint all_different (l : list ascii) : Prop :=
  match l with
  | nil => True
  | h :: t => ~In h t /\ all_different t
  end.

(* Helper to get index of second occurrence *)
Fixpoint findIdx_second (c : ascii) (l : list ascii) (firstIdx : nat) (currentIdx : nat) : nat :=
  match l with
  | nil => 0%nat
  | h :: t =>
      if ascii_dec h c then
        if Nat.eqb currentIdx firstIdx then
          findIdx_second c t firstIdx (S currentIdx)
        else
          currentIdx
      else
        findIdx_second c t firstIdx (S currentIdx)
  end.

(* Take first n elements *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0%nat, _ => nil
  | S n', h :: t => h :: take n' t
  | _, nil => nil
  end.

Definition findFirstRepeatedChar_postcond_dec (s : string) (result : option ascii) : bool :=
  true.
(* !benchmark @end postcond_aux *)

Definition findFirstRepeatedChar_postcond (s : string) (result : (option ascii)) (h_precond : findFirstRepeatedChar_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let cs := string_to_list s in
  match result with
  | Some c =>
      let firstIdx := indexOf_char c cs in
      let secondIdx := findIdx_second c cs firstIdx 0%nat in
      (count_char c cs >= 2)%nat /\
      all_different (take secondIdx cs)
  | None =>
      all_different cs
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstRepeatedChar_postcond_satisfied (s : string) (h_precond : findFirstRepeatedChar_precond s) :
    findFirstRepeatedChar_postcond s (findFirstRepeatedChar s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
