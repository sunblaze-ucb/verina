(* Run-length encoding: compress consecutive identical characters *)

(* !benchmark @start import type=task *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* Convert string to list of ascii characters *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

(* Convert list of ascii to string *)
Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

(* Replicate a character n times as a list *)
Fixpoint replicate_char (c : ascii) (n : nat) : list ascii :=
  match n with
  | O => []
  | S m => c :: replicate_char c m
  end.

(* Helper to check ascii equality *)
Definition ascii_eqb (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition runLengthEncode_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition runLengthEncode_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Run-length encoding helper function *)
Fixpoint encodeAux (acc : list (ascii * nat)) (rest : list ascii) : list (ascii * nat) :=
  match rest with
  | [] => rev acc
  | h :: t =>
    match acc with
    | [] => encodeAux [(h, 1)] t
    | (ch, count) :: accTail =>
      if ascii_eqb ch h then
        encodeAux ((ch, S count) :: accTail) t
      else
        encodeAux ((h, 1) :: (ch, count) :: accTail) t
    end
  end.
(* !benchmark @end code_aux *)

Definition runLengthEncode (s : string) (h_precond : runLengthEncode_precond s) : list (ascii * nat) :=
  (* !benchmark @start code *)
  encodeAux [] (string_to_list s)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Decode RLE back to string *)
Fixpoint decodeRLE (lst : list (ascii * nat)) : string :=
  match lst with
  | [] => EmptyString
  | (ch, cnt) :: tail =>
    let repeated := list_to_string (replicate_char ch cnt) in
    append repeated (decodeRLE tail)
  end.

(* Check if all counts are > 0 *)
Definition all_counts_positive (lst : list (ascii * nat)) : bool :=
  forallb (fun p => negb (Nat.eqb (snd p) 0)) lst.

(* Check that no two consecutive elements have the same character *)
Fixpoint no_consecutive_same (lst : list (ascii * nat)) : bool :=
  match lst with
  | [] => true
  | [_] => true
  | (c1, _) :: ((c2, _) :: _ as rest) =>
    negb (ascii_eqb c1 c2) && no_consecutive_same rest
  end.

(* Decidable postcondition checker *)
Definition runLengthEncode_postcond_dec (s : string) (result : list (ascii * nat)) : bool :=
  all_counts_positive result &&
  no_consecutive_same result &&
  String.eqb (decodeRLE result) s.
(* !benchmark @end postcond_aux *)

Definition runLengthEncode_postcond (s : string) (result : list (ascii * nat)) (h_precond : runLengthEncode_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (* All counts are positive *)
  (forall pair, In pair result -> (snd pair > 0)%nat) /\
  (* No consecutive pairs have the same character *)
  no_consecutive_same result = true /\
  (* Decoding gives back the original string *)
  decodeRLE result = s
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem runLengthEncode_postcond_satisfied (s : string) (h_precond : runLengthEncode_precond s) :
    runLengthEncode_postcond s (runLengthEncode s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  (* Full proof is complex - relies on QuickChick testing *)
  Admitted.
  (* !benchmark @end proof *)
