(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint all_chars_binary (l : list ascii) : bool :=
  match l with
  | [] => true
  | c :: cs => (Ascii.eqb c "0"%char || Ascii.eqb c "1"%char) && all_chars_binary cs
  end.

Definition shortestBeautifulSubstring_precond_dec (s : string) (k : nat) : bool :=
  all_chars_binary (list_ascii_of_string s).
(* !benchmark @end precond_aux *)

Definition shortestBeautifulSubstring_precond (s : string) (k : nat) : Prop :=
  (* !benchmark @start precond *)
  shortestBeautifulSubstring_precond_dec s k = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countOnes (lst : list ascii) : nat :=
  match lst with
  | [] => 0%nat
  | c :: cs => if Ascii.eqb c "1"%char then S (countOnes cs) else countOnes cs
  end.

Definition listToString (lst : list ascii) : string :=
  string_of_list_ascii lst.

Definition isLexSmaller (a b : list ascii) : bool :=
  String.ltb (listToString a) (listToString b).

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0%nat => []
  | S n' => range n' ++ [n']
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0%nat, _ => l
  | S n', [] => []
  | S n', _ :: l' => drop n' l'
  end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0%nat, _ => []
  | S n', [] => []
  | S n', x :: l' => x :: take n' l'
  end.

Definition allSubstrings (s : list ascii) : list (list ascii) :=
  let n := length s in
  flat_map (fun i =>
    map (fun j =>
      take (j + 1) (drop i s))
    (range (n - i)))
  (range n).

Definition compare_substrings (a b : list ascii) : bool :=
  (length a <? length b)%nat || ((length a =? length b)%nat && isLexSmaller a b).

Fixpoint foldl_option {A : Type} (f : option A -> A -> option A) (acc : option A) (l : list A) : option A :=
  match l with
  | [] => acc
  | x :: xs => foldl_option f (f acc x) xs
  end.
(* !benchmark @end code_aux *)

Definition shortestBeautifulSubstring (s : string) (k : nat) (h_precond : shortestBeautifulSubstring_precond s k) : string :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string s in
  let candidates := filter (fun sub => Nat.eqb (countOnes sub) k) (allSubstrings chars) in
  let best := foldl_option (fun acc cur =>
    match acc with
    | None => Some cur
    | Some best => if compare_substrings cur best then Some cur else Some best
    end) None candidates in
  match best with
  | Some b => listToString b
  | None => ""%string
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition shortestBeautifulSubstring_postcond_dec (s : string) (k : nat) (result : string) : bool :=
  let chars := list_ascii_of_string s in
  let substrings := flat_map (fun i =>
    map (fun len => take len (drop i chars))
    (range (length chars - i + 1)))
  (range (length chars)) in
  let isBeautiful := fun sub => Nat.eqb (countOnes sub) k in
  let beautiful := filter isBeautiful substrings in
  let targets := filter (fun ss => negb (String.eqb ss ""%string)) 
                   (map (fun sub => string_of_list_ascii sub) beautiful) in
  (String.eqb result ""%string && (length targets =? 0)%nat) ||
  (existsb (String.eqb result) targets &&
   forallb (fun r => 
     (String.length result <=? String.length r)%nat ||
     ((String.length result =? String.length r)%nat && String.leb result r))
   targets).
(* !benchmark @end postcond_aux *)

Definition shortestBeautifulSubstring_postcond (s : string) (k : nat) (result : string) (h_precond : shortestBeautifulSubstring_precond s k) : Prop :=
  (* !benchmark @start postcond *)
  let chars := list_ascii_of_string s in
  let substrings := flat_map (fun i =>
    map (fun len => take len (drop i chars))
    (range (length chars - i + 1)))
  (range (length chars)) in
  let isBeautiful := fun sub => Nat.eqb (countOnes sub) k in
  let beautiful := filter isBeautiful substrings in
  let targets := filter (fun ss => negb (String.eqb ss ""%string)) 
                   (map (fun sub => string_of_list_ascii sub) beautiful) in
  (result = ""%string /\ targets = []) \/
  (In result targets /\
   forall r, In r targets -> (String.length r >= String.length result)%nat \/ 
     (String.length r = String.length result /\ String.leb result r = true))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem shortestBeautifulSubstring_postcond_satisfied (s : string) (k : nat) (h_precond : shortestBeautifulSubstring_precond s k) :
    shortestBeautifulSubstring_postcond s k (shortestBeautifulSubstring s k h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
