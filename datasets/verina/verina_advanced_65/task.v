(* !benchmark @start import type=task *)
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

Definition reverseString_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint reverseAux (chars : list ascii) (acc : list ascii) : list ascii :=
  match chars with
  | [] => acc
  | h :: t => reverseAux t (h :: acc)
  end.

Definition list_ascii_of_string (s : string) : list ascii :=
  let fix go (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c rest => c :: go rest
    end
  in go s.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (string_of_list_ascii rest)
  end.
(* !benchmark @end code_aux *)

Definition reverseString (s : string) : string :=
  (* !benchmark @start code *)
  string_of_list_ascii (reverseAux (list_ascii_of_string s) [])
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition string_length (s : string) : nat :=
  let fix go (s : string) : nat :=
    match s with
    | EmptyString => O
    | String _ rest => S (go rest)
    end
  in go s.

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (Ascii.eqb h1 h2) && list_ascii_eqb t1 t2
  | _, _ => false
  end.

Definition list_ascii_of_string' (s : string) : list ascii :=
  let fix go (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c rest => c :: go rest
    end
  in go s.
(* !benchmark @end postcond_aux *)

Definition reverseString_postcond (s : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  (string_length result =? string_length s)%nat && list_ascii_eqb (list_ascii_of_string' result) (rev (list_ascii_of_string' s))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem reverseString_postcond_satisfied (s : string) :
    reverseString_precond s = true ->
    reverseString_postcond s (reverseString s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
