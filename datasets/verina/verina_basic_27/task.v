(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Require Import String.
Require Import Ascii.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Nat.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint ascii_eqb (a b : ascii) : bool :=
  match a, b with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3 && Bool.eqb a4 b4 &&
    Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7 && Bool.eqb a8 b8
  end.

Fixpoint mem_ascii (c : ascii) (seen : list ascii) : bool :=
  match seen with
  | [] => false
  | h :: t => if ascii_eqb c h then true else mem_ascii c t
  end.

Definition list_ascii_of_string (s : string) : list ascii :=
  let fix aux (s : string) (acc : list ascii) : list ascii :=
    match s with
    | EmptyString => rev acc
    | String c rest => aux rest (c :: acc)
    end
  in aux s [].
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition findFirstRepeatedChar_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint findFirstRepeatedChar_loop (cs : list ascii) (seen : list ascii) : option ascii :=
  match cs with
  | [] => None
  | c :: rest =>
    if mem_ascii c seen then Some c
    else findFirstRepeatedChar_loop rest (c :: seen)
  end.
(* !benchmark @end code_aux *)

Definition findFirstRepeatedChar (s : string) : (option ascii) :=
  (* !benchmark @start code *)
  findFirstRepeatedChar_loop (list_ascii_of_string s) []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_ascii (c : ascii) (cs : list ascii) : nat :=
  match cs with
  | [] => O
  | h :: t => if ascii_eqb c h then S (count_ascii c t) else count_ascii c t
  end.

Fixpoint idxOf_ascii (c : ascii) (cs : list ascii) : nat :=
  match cs with
  | [] => O
  | h :: t => if ascii_eqb c h then O else S (idxOf_ascii c t)
  end.

Fixpoint findIdx_aux {A : Type} (p : A -> nat -> bool) (cs : list A) (idx : nat) : nat :=
  match cs with
  | [] => idx
  | h :: t => if p h idx then idx else findIdx_aux p t (S idx)
  end.

Definition findIdx {A : Type} (p : A -> nat -> bool) (cs : list A) : nat :=
  findIdx_aux p cs O.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | h :: t => h :: take n' t
            end
  end.

Fixpoint pairwise_distinct (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | h :: t => negb (mem_ascii h t) && pairwise_distinct t
  end.

Definition list_ascii_of_string_post (s : string) : list ascii :=
  let fix aux (s : string) (acc : list ascii) : list ascii :=
    match s with
    | EmptyString => rev acc
    | String c rest => aux rest (c :: acc)
    end
  in aux s [].
(* !benchmark @end postcond_aux *)

Definition findFirstRepeatedChar_postcond (s : string) (result : (option ascii)) : bool :=
  (* !benchmark @start postcond *)
  let cs := list_ascii_of_string_post s in
  match result with
  | Some c =>
    let firstIdx := idxOf_ascii c cs in
    let secondIdx := findIdx (fun x i => ascii_eqb x c && negb (i =? firstIdx)%nat) cs in
    (2 <=? count_ascii c cs)%nat && pairwise_distinct (take secondIdx cs)
  | None => pairwise_distinct cs
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findFirstRepeatedChar_postcond_satisfied (s : string) :
    findFirstRepeatedChar_precond s = true ->
    findFirstRepeatedChar_postcond s (findFirstRepeatedChar s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
