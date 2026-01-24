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
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n)%nat && (n <=? 57)%nat).
(* !benchmark @end precond_aux *)

Definition runLengthEncoder_precond (input : string) : bool :=
  (* !benchmark @start precond *)
  forallb (fun c => negb (isDigit c)) (list_ascii_of_string input)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition ascii_eqb (c1 c2 : ascii) : bool :=
  (nat_of_ascii c1 =? nat_of_ascii c2)%nat.

Fixpoint digitsAux (fuel : nat) (n : nat) (acc : list ascii) : list ascii :=
  match fuel with
  | O => acc
  | S fuel' =>
    match n with
    | O => acc
    | _ => 
      let digit := ascii_of_nat ((n mod 10)%nat + 48)%nat in
      digitsAux fuel' (n / 10)%nat (digit :: acc)
    end
  end.

Definition natToString (n : nat) : string :=
  match n with
  | O => "0"
  | _ => string_of_list_ascii (digitsAux n n [])
  end.

Fixpoint encode (input : list ascii) (currentChar : option ascii) (count : nat) : string :=
  match input with
  | [] =>
    match currentChar with
    | None => ""
    | Some c => String c (natToString count)
    end
  | c :: rest =>
    match currentChar with
    | None => encode rest (Some c) 1%nat
    | Some c' =>
      if ascii_eqb c c' then
        encode rest (Some c') (count + 1)%nat
      else
        let currentPart := String c' (natToString count) in
        append currentPart (encode rest (Some c) 1%nat)
    end
  end.
(* !benchmark @end code_aux *)

Definition runLengthEncoder (input : string) : string :=
  (* !benchmark @start code *)
  match list_ascii_of_string input with
  | [] => ""
  | c :: rest => encode rest (Some c) 1%nat
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition isDigit_post (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n)%nat && (n <=? 57)%nat).

Fixpoint parseState (remaining : list ascii) (currentChar : option ascii) (currentCount : option nat) (acc : list (ascii * nat)) : list (ascii * nat) :=
  match remaining with
  | [] =>
    match currentChar, currentCount with
    | Some c, Some n => (c, n) :: acc
    | _, _ => acc
    end
  | c :: cs =>
    if isDigit_post c then
      match currentChar with
      | None => [] (* Invalid format *)
      | Some ch =>
        let digit := (nat_of_ascii c - 48)%nat in
        let newCount :=
          match currentCount with
          | None => digit
          | Some n => (n * 10 + digit)%nat
          end
        in parseState cs currentChar (Some newCount) acc
      end
    else
      let newAcc :=
        match currentChar, currentCount with
        | Some ch, Some n => (ch, n) :: acc
        | _, _ => acc
        end
      in parseState cs (Some c) None newAcc
  end.

Definition parseEncodedString (s : string) : list (ascii * nat) :=
  rev (parseState (list_ascii_of_string s) None None []).

Fixpoint checkPairs (chars : list ascii) (nowDigit : bool) : bool :=
  match chars with
  | [] => true
  | c :: cs =>
    if nowDigit && isDigit_post c then
      checkPairs cs true
    else
      match cs with
      | [] => false
      | d :: ds =>
        if isDigit_post d then
          checkPairs ds true
        else
          false
      end
  end.

Fixpoint replicate_ascii (n : nat) (c : ascii) : list ascii :=
  match n with
  | O => []
  | S n' => c :: replicate_ascii n' c
  end.

Fixpoint expand (pairs : list (ascii * nat)) : list ascii :=
  match pairs with
  | [] => []
  | (c, n) :: rest => replicate_ascii n c ++ expand rest
  end.

Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => ((nat_of_ascii h1 =? nat_of_ascii h2)%nat && list_ascii_eqb t1 t2)
  | _, _ => false
  end.

Definition string_isEmpty (s : string) : bool :=
  match s with
  | EmptyString => true
  | _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition runLengthEncoder_postcond (input : string) (result : string) : bool :=
  (* !benchmark @start postcond *)
  let formatValid := 
    if string_isEmpty result then true
    else checkPairs (list_ascii_of_string result) false in
  let pairs := parseEncodedString result in
  let expanded := expand pairs in
  let contentValid := list_ascii_eqb expanded (list_ascii_of_string input) in
  let nonEmptyValid := Bool.eqb (string_isEmpty input) (string_isEmpty result) in
  formatValid && contentValid && nonEmptyValid
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem runLengthEncoder_postcond_satisfied (input : string) :
    runLengthEncoder_precond input = true ->
    runLengthEncoder_postcond input (runLengthEncoder input) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
