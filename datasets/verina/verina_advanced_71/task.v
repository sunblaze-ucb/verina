(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Require Import String.
Require Import Ascii.
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
Definition is_binary_char (c : ascii) : bool :=
  (Nat.eqb (nat_of_ascii c) (nat_of_ascii "0"%char)) ||
  (Nat.eqb (nat_of_ascii c) (nat_of_ascii "1"%char)).
(* !benchmark @end precond_aux *)

Definition shortestBeautifulSubstring_precond (s : string) (k : nat) : bool :=
  (* !benchmark @start precond *)
  forallb is_binary_char (list_ascii_of_string s)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition countOnes (lst : list ascii) : nat :=
  fold_left (fun acc c => if Nat.eqb (nat_of_ascii c) (nat_of_ascii "1"%char) then (acc + 1)%nat else acc) lst O.

Definition listToString (lst : list ascii) : string :=
  string_of_list_ascii lst.

Fixpoint string_ltb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => false
  | EmptyString, _ => true
  | _, EmptyString => false
  | String c1 r1, String c2 r2 =>
    if Nat.ltb (nat_of_ascii c1) (nat_of_ascii c2) then true
    else if Nat.ltb (nat_of_ascii c2) (nat_of_ascii c1) then false
    else string_ltb r1 r2
  end.

Definition isLexSmaller (a b : list ascii) : bool :=
  string_ltb (listToString a) (listToString b).

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S m => range m ++ [m]
  end.

Definition allSubstrings (chars : list ascii) : list (list ascii) :=
  let n := List.length chars in
  flat_map (fun i =>
    map (fun j => firstn (j + 1)%nat (skipn i chars)) (range (n - i)%nat)
  ) (range n).

Definition compare_subs (a b : list ascii) : bool :=
  (Nat.ltb (List.length a) (List.length b)) ||
  ((Nat.eqb (List.length a) (List.length b)) && (isLexSmaller a b)).

Definition find_best (candidates : list (list ascii)) : option (list ascii) :=
  fold_left (fun acc cur =>
    match acc with
    | None => Some cur
    | Some best => if compare_subs cur best then Some cur else Some best
    end
  ) candidates None.
(* !benchmark @end code_aux *)

Definition shortestBeautifulSubstring (s : string) (k : nat) : string :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string s in
  let candidates := filter (fun sub => Nat.eqb (countOnes sub) k) (allSubstrings chars) in
  match find_best candidates with
  | Some b => listToString b
  | None => EmptyString
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition countOnes_post (lst : list ascii) : nat :=
  fold_left (fun acc c => if Nat.eqb (nat_of_ascii c) (nat_of_ascii "1"%char) then (acc + 1)%nat else acc) lst O.

Fixpoint range_post (n : nat) : list nat :=
  match n with
  | O => []
  | S m => range_post m ++ [m]
  end.

Definition allSubstrings_post (chars : list ascii) : list (list ascii) :=
  let n := List.length chars in
  flat_map (fun i =>
    map (fun len => firstn len (skipn i chars)) (range_post (n - i + 1)%nat)
  ) (range_post n).

Definition isBeautiful_post (sub : list ascii) (k : nat) : bool :=
  Nat.eqb (countOnes_post sub) k.

Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 r1, String c2 r2 => (Nat.eqb (nat_of_ascii c1) (nat_of_ascii c2)) && string_eqb r1 r2
  | _, _ => false
  end.

Fixpoint string_leb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | _, EmptyString => false
  | String c1 r1, String c2 r2 =>
    if Nat.ltb (nat_of_ascii c1) (nat_of_ascii c2) then true
    else if Nat.ltb (nat_of_ascii c2) (nat_of_ascii c1) then false
    else string_leb r1 r2
  end.

Definition string_mem (s : string) (l : list string) : bool :=
  existsb (fun x => string_eqb x s) l.

Definition check_best (result : string) (targets : list string) : bool :=
  forallb (fun r => 
    (Nat.ltb (String.length result) (String.length r)) ||
    ((Nat.eqb (String.length r) (String.length result)) && string_leb result r))
  targets.
(* !benchmark @end postcond_aux *)

Definition shortestBeautifulSubstring_postcond (s : string) (k : nat) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let chars := list_ascii_of_string s in
    let substrings := allSubstrings_post chars in
    let beautiful := filter (fun sub => isBeautiful_post sub k) substrings in
    let targets := filter (fun s => negb (string_eqb s EmptyString)) (map string_of_list_ascii beautiful) in
    ((string_eqb result EmptyString) && (Nat.eqb (List.length targets) O)) ||
    ((string_mem result targets) && (check_best result targets))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem shortestBeautifulSubstring_postcond_satisfied (s : string) (k : nat) :
    shortestBeautifulSubstring_precond s k = true ->
    shortestBeautifulSubstring_postcond s k (shortestBeautifulSubstring s k) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
