(* !benchmark @start import type=task *)
Require Import List.
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

Definition insert_precond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) : bool :=
  (* !benchmark @start precond *)
  (l <=? length oline)%nat && (p <=? length nl)%nat && (atPos <=? l)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_default_ascii (n : nat) (l : list ascii) (default : ascii) : ascii :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_ascii n' t default
              end
  end.

Definition get_char (l : list ascii) (i : nat) : ascii :=
  nth_default_ascii i l " "%char.

Fixpoint set_nth (l : list ascii) (i : nat) (c : ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t => match i with
              | O => c :: t
              | S i' => h :: set_nth t i' c
              end
  end.

Fixpoint repeat_char (c : ascii) (n : nat) : list ascii :=
  match n with
  | O => []
  | S n' => c :: repeat_char c n'
  end.

Fixpoint fold_range (n : nat) (f : list ascii -> nat -> list ascii) (acc : list ascii) : list ascii :=
  match n with
  | O => acc
  | S n' => f (fold_range n' f acc) n'
  end.
(* !benchmark @end code_aux *)

Definition insert (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) : (list ascii) :=
  (* !benchmark @start code *)
  let result := repeat_char " "%char (l + p) in
  let result := fold_range l (fun acc i =>
    if (i <? atPos)%nat then set_nth acc i (get_char oline i) else acc) result in
  let result := fold_range p (fun acc i =>
    set_nth acc (atPos + i) (get_char nl i)) result in
  let result := fold_range l (fun acc i =>
    if (atPos <=? i)%nat then set_nth acc (i + p) (get_char oline i) else acc) result in
  result
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_ascii_post (n : nat) (l : list ascii) (default : ascii) : ascii :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_ascii_post n' t default
              end
  end.

Definition get_char_post (l : list ascii) (i : nat) : ascii :=
  nth_default_ascii_post i l " "%char.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Definition ascii_eqb (a b : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) (nat_of_ascii b).
(* !benchmark @end postcond_aux *)

Definition insert_postcond (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) (result : (list ascii)) : bool :=
  (* !benchmark @start postcond *)
  (length result =? l + p)%nat &&
  forallb (fun i => ascii_eqb (get_char_post result (atPos + i)) (get_char_post nl i)) (range p) &&
  forallb (fun i => ascii_eqb (get_char_post result i) (get_char_post oline i)) (range atPos) &&
  forallb (fun i => ascii_eqb (get_char_post result (atPos + p + i)) (get_char_post oline (atPos + i))) (range (l - atPos))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem insert_postcond_satisfied (oline : (list ascii)) (l : nat) (nl : (list ascii)) (p : nat) (atPos : nat) :
    insert_precond oline l nl p atPos = true ->
    insert_postcond oline l nl p atPos (insert oline l nl p atPos) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
