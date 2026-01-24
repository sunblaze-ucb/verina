(* !benchmark @start import type=task *)
Require Import Bool.
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Fixpoint list_list_nat_eqb (l1 l2 : list (list nat)) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => list_nat_eqb h1 h2 && list_list_nat_eqb t1 t2
  | _, _ => false
  end.

Definition nth_nat (l : list nat) (n : nat) : nat :=
  nth n l 0%nat.

Fixpoint nodup_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (fun y => (x =? y)%nat) xs) && nodup_nat xs
  end.

Fixpoint flatMap_nat {A : Type} (f : A -> list nat) (l : list A) : list nat :=
  match l with
  | [] => []
  | x :: xs => f x ++ flatMap_nat f xs
  end.
(* !benchmark @end precond_aux *)

Definition hasChordIntersection_precond (N : nat) (chords : (list (list nat))) : bool :=
  (* !benchmark @start precond *)
  (2 <=? N)%nat &&
  forallb (fun chord => 
    ((length chord =? 2)%nat &&
     (1 <=? nth_nat chord 0)%nat && (nth_nat chord 0 <=? 2 * N)%nat &&
     (1 <=? nth_nat chord 1)%nat && (nth_nat chord 1 <=? 2 * N)%nat)) chords &&
  nodup_nat (flatMap_nat (fun x => x) chords)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition get_nat (l : list nat) (n : nat) : nat :=
  nth n l 0%nat.

Definition sortChord (chord : list nat) : list nat :=
  let a := get_nat chord 0 in
  let b := get_nat chord 1 in
  if (b <? a)%nat then [b; a] else [a; b].

Fixpoint dropWhile_chord (f : list nat -> bool) (l : list (list nat)) : list (list nat) :=
  match l with
  | [] => []
  | x :: xs => if f x then dropWhile_chord f xs else x :: xs
  end.

Fixpoint checkIntersection (stack : list (list nat)) (remaining : list (list nat)) : bool :=
  match remaining with
  | [] => false
  | chord :: rest =>
    let a := get_nat chord 0 in
    let b := get_nat chord 1 in
    let newStack := dropWhile_chord (fun c => (get_nat c 1 <? a)%nat) stack in
    match newStack with
    | [] => checkIntersection (chord :: newStack) rest
    | top :: _ =>
      let topB := get_nat top 1 in
      if (a <? topB)%nat && (topB <? b)%nat then true
      else checkIntersection (chord :: newStack) rest
    end
  end.

Fixpoint insert_chord (x : list nat) (xs : list (list nat)) : list (list nat) :=
  match xs with
  | [] => [x]
  | y :: ys => if (get_nat x 0 <? get_nat y 0)%nat then x :: xs else y :: insert_chord x ys
  end.

Fixpoint sort_chords (xs : list (list nat)) : list (list nat) :=
  match xs with
  | [] => []
  | x :: rest => insert_chord x (sort_chords rest)
  end.
(* !benchmark @end code_aux *)

Definition hasChordIntersection (N : nat) (chords : (list (list nat))) : bool :=
  (* !benchmark @start code *)
  let sortedChords := map sortChord chords in
  let sortedChords2 := sort_chords sortedChords in
  checkIntersection [] sortedChords2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition get_nat_post (l : list nat) (n : nat) : nat :=
  nth n l 0%nat.

Definition sortChord_post (chord : list nat) : list nat :=
  let a := get_nat_post chord 0 in
  let b := get_nat_post chord 1 in
  if (b <? a)%nat then [b; a] else [a; b].

Definition hasIntersection (chord1 chord2 : list nat) : bool :=
  let a1 := get_nat_post chord1 0 in
  let b1 := get_nat_post chord1 1 in
  let a2 := get_nat_post chord2 0 in
  let b2 := get_nat_post chord2 1 in
  ((a1 <? a2)%nat && (a2 <? b1)%nat && (b1 <? b2)%nat) ||
  ((a2 <? a1)%nat && (a1 <? b2)%nat && (b2 <? b1)%nat).

Fixpoint pairwiseNoIntersect (chords : list (list nat)) : bool :=
  match chords with
  | [] => true
  | x :: xs => forallb (fun y => negb (hasIntersection x y)) xs && pairwiseNoIntersect xs
  end.

Definition anyIntersects (sortedChords originalChords : list (list nat)) : bool :=
  existsb (fun x => existsb (fun y => hasIntersection x y) originalChords) sortedChords.
(* !benchmark @end postcond_aux *)

Definition hasChordIntersection_postcond (N : nat) (chords : (list (list nat))) (result : bool) : bool :=
  (* !benchmark @start postcond *)
  let sortedChords := map sortChord_post chords in
  implb (pairwiseNoIntersect sortedChords) (negb result) &&
  implb (anyIntersects sortedChords chords) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasChordIntersection_postcond_satisfied (N : nat) (chords : (list (list nat))) :
    hasChordIntersection_precond N chords = true ->
    hasChordIntersection_postcond N chords (hasChordIntersection N chords) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
