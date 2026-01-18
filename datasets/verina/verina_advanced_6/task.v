(* !benchmark @start import type=task *)
Require Import Bool.
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* empty *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Definition toLower (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (Nat.leb 65 n) && (Nat.leb n 90) then
    ascii_of_nat (n + 32)
  else
    c.

Fixpoint normalize_str (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => toLower c :: normalize_str s'
  end.

Definition ascii_eqb (a b : ascii) : bool :=
  if ascii_dec a b then true else false.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition allVowels_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition allVowels_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint contains {A : Type} (eqb : A -> A -> bool) (l : list A) (x : A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eqb x y then true else contains eqb ys x
  end.

Fixpoint all {A : Type} (l : list A) (f : A -> bool) : bool :=
  match l with
  | [] => true
  | x :: xs => if f x then all xs f else false
  end.
(* !benchmark @end code_aux *)

Definition allVowels (s : string) (h_precond : allVowels_precond s) : bool :=
  (* !benchmark @start code *)
  let chars := normalize_str s in
  let vowelSet := [ascii_of_nat 97; ascii_of_nat 101; ascii_of_nat 105; 
                   ascii_of_nat 111; ascii_of_nat 117] in
  all vowelSet (fun v => contains ascii_eqb chars v)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition allVowels_postcond_dec (s : string) (result : bool) : bool :=
  let chars := normalize_str s in
  let vowelSet := [ascii_of_nat 97; ascii_of_nat 101; ascii_of_nat 105; 
                   ascii_of_nat 111; ascii_of_nat 117] in
  Bool.eqb result (all vowelSet (fun v => contains ascii_eqb chars v)).
(* !benchmark @end postcond_aux *)

Definition allVowels_postcond (s : string) (result : bool) (h_precond : allVowels_precond s) : Prop :=
  (* !benchmark @start postcond *)
  let chars := normalize_str s in
  let vowelSet := [ascii_of_nat 97; ascii_of_nat 101; ascii_of_nat 105; 
                   ascii_of_nat 111; ascii_of_nat 117] in
  (result = true <-> all vowelSet (fun v => contains ascii_eqb chars v) = true)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem allVowels_postcond_satisfied (s : string) (h_precond : allVowels_precond s) :
    allVowels_postcond s (allVowels s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
