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

(* !benchmark @end precond_aux *)

Definition runLengthEncode_precond (s : string) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint encodeAux (acc : list (ascii * nat)) (rest : list ascii) : list (ascii * nat) :=
  match rest with
  | [] => rev acc
  | h :: t =>
    match acc with
    | (ch, count) :: accTail =>
      if (Ascii.eqb ch h) then
        encodeAux ((ch, (count + 1)%nat) :: accTail) t
      else
        encodeAux ((h, 1%nat) :: (ch, count) :: accTail) t
    | [] =>
      encodeAux [(h, 1%nat)] t
    end
  end.
(* !benchmark @end code_aux *)

Definition runLengthEncode (s : string) : list (ascii * nat) :=
  (* !benchmark @start code *)
  let chars := list_ascii_of_string s in
  encodeAux [] chars
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint decodeRLE (lst : list (ascii * nat)) : string :=
  match lst with
  | [] => EmptyString
  | (ch, cnt) :: tail =>
    let fix repeatChar (c : ascii) (n : nat) : list ascii :=
      match n with
      | O => []
      | S n' => c :: repeatChar c n'
      end
    in
    append (string_of_list_ascii (repeatChar ch cnt)) (decodeRLE tail)
  end.

Fixpoint allPositiveCounts (lst : list (ascii * nat)) : bool :=
  match lst with
  | [] => true
  | (_, cnt) :: tail => (1 <=? cnt)%nat && allPositiveCounts tail
  end.

Definition ascii_eqb (a b : ascii) : bool := Ascii.eqb a b.

Fixpoint noConsecutiveSameChar (lst : list (ascii * nat)) : bool :=
  match lst with
  | [] => true
  | [_] => true
  | (ch1, _) :: ((ch2, cnt2) :: rest as tail) =>
    negb (ascii_eqb ch1 ch2) && noConsecutiveSameChar tail
  end.

Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 t1, String c2 t2 => Ascii.eqb c1 c2 && string_eqb t1 t2
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition runLengthEncode_postcond (s : string) (result : list (ascii * nat)) : bool :=
  (* !benchmark @start postcond *)
  allPositiveCounts result && noConsecutiveSameChar result && string_eqb (decodeRLE result) s
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem runLengthEncode_postcond_satisfied (s : string) :
    runLengthEncode_precond s = true ->
    runLengthEncode_postcond s (runLengthEncode s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
