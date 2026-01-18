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
(* No task-level type definitions *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* No solution-level auxiliary definitions *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint string_all (s : string) (p : ascii -> bool) : bool :=
  match s with
  | EmptyString => true
  | String c s' => p c && string_all s' p
  end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n) && (n <=? 57).

Definition runLengthEncoder_precond_dec (input : string) : bool :=
  string_all input (fun c => negb (is_digit c)).
(* !benchmark @end precond_aux *)

Definition runLengthEncoder_precond (input : string) : Prop :=
  (* !benchmark @start precond *)
  runLengthEncoder_precond_dec input = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
```coq
Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_of_string s'
  end.

Definition string_of_list (l : list ascii) : string :=
  fold_right String EmptyString l.

Definition char_eqb (c1 c2 : ascii) : bool :=
  if ascii_dec c1 c2 then true else false.

Fixpoint nat_to_digits_acc (fuel n : nat) (acc : list ascii) : list ascii :=
  match fuel with
  | 0%nat => acc
  | S fuel' =>
    match n with
    | 0%nat => acc
    | _ => 
      let digit := ascii_of_nat (n mod 10 + 48) in
      nat_to_digits_acc fuel' (n / 10) (digit :: acc)
    end
  end.

Definition nat_to_digits (n : nat) : list ascii :=
  match n with
  | 0%nat => []
  | _ => nat_to_digits_acc n n []
  end.

Definition nat_to_string (n : nat) : string :=
  string_of_list (nat_to_digits n).

Fixpoint encode_helper (input : list ascii) (currentChar : option ascii) (count : nat) : string :=
  match input with
  | [] =>
    match currentChar with
    | None => EmptyString
    | Some c => String c (nat_to_string count)
    end
  | c :: rest =>
    match currentChar with
    | None => encode_helper rest (Some c) 1%nat
    | Some c' =>
      if char_eqb c c' then
        encode_helper rest (Some c') (count + 1)
      else
        let currentPart := String c' (nat_to_string count) in
        currentPart ++ (encode_helper rest (Some c) 1%nat)
    end
  end.

Fixpoint list_head_option {A : Type} (l : list A) : option A :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

Fixpoint list_tail {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | _ :: xs => xs
  end.

Definition string_is_empty (s : string) : bool :=
  match s with
  | EmptyString => true
  | _ => false
  end.
```

The key changes:
1. Changed `String c' EmptyString` to just `String c'` (using the String constructor properly)
2. Changed `(String c EmptyString) ++ (nat_to_string count)` to `String c (nat_to_string count)` - directly building the string
3. Changed `(String c' EmptyString) ++ (nat_to_string count)` to `String c' (nat_to_string count)`

This fixes the type mismatch by properly using the `String` constructor which takes an `ascii` and a `string` to produce a `string`.
(* !benchmark @end code_aux *)

Definition runLengthEncoder (input : string) (h_precond : runLengthEncoder_precond input) : string :=
  (* !benchmark @start code *)
  let chars := list_of_string input in
  if string_is_empty input then
    EmptyString
  else
    let firstChar := list_head_option chars in
    encode_helper (list_tail chars) firstChar 1%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint parse_state (remaining : list ascii) (currentChar : option ascii) 
                     (currentCount : option nat) (acc : list (ascii * nat)) 
                     : list (ascii * nat) :=
  match remaining with
  | [] =>
    match currentChar, currentCount with
    | Some c, Some n => (c, n) :: acc
    | _, _ => acc
    end
  | c :: cs =>
    if is_digit c then
      match currentChar with
      | None => []
      | Some ch =>
        let digit := nat_of_ascii c - 48 in
        let newCount :=
          match currentCount with
          | None => digit
          | Some n => n * 10 + digit
          end in
        parse_state cs (Some ch) (Some newCount) acc
      end
    else
      let newAcc :=
        match currentChar, currentCount with
        | Some ch, Some n => (ch, n) :: acc
        | _, _ => acc
        end in
      parse_state cs (Some c) None newAcc
  end.

Definition parse_encoded_string (s : string) : list (ascii * nat) :=
  let result := parse_state (list_of_string s) None None [] in
  rev result.

Fixpoint check_pairs (chars : list ascii) (nowDigit : bool) : bool :=
  match chars with
  | [] => true
  | c :: cs =>
    if nowDigit && is_digit c then
      check_pairs cs true
    else
      match cs with
      | [] => false
      | d :: ds =>
        if is_digit d then
          check_pairs ds true
        else
          false
      end
  end.

Definition format_valid (result : string) : bool :=
  check_pairs (list_of_string result) false.

Fixpoint replicate {A : Type} (n : nat) (a : A) : list A :=
  match n with
  | 0%nat => []
  | S n' => a :: replicate n' a
  end.

Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

Fixpoint list_eqb_ascii (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => char_eqb x y && list_eqb_ascii xs ys
  | _, _ => false
  end.

Definition content_valid (input result : string) : bool :=
  let pairs := parse_encoded_string result in
  let expanded := flat_map (fun p => replicate (snd p) (fst p)) pairs in
  list_eqb_ascii expanded (list_of_string input).

Definition non_empty_valid (input result : string) : bool :=
  Bool.eqb (string_is_empty input) (string_is_empty result).

Definition runLengthEncoder_postcond_dec (input : string) (result : string) : bool :=
  format_valid result && content_valid input result && non_empty_valid input result.
(* !benchmark @end postcond_aux *)

Definition runLengthEncoder_postcond (input : string) (result : string) (h_precond : runLengthEncoder_precond input) : Prop :=
  (* !benchmark @start postcond *)
  runLengthEncoder_postcond_dec input result = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem runLengthEncoder_postcond_satisfied (input : string) (h_precond : runLengthEncoder_precond input) :
    runLengthEncoder_postcond input (runLengthEncoder input h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
